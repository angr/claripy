import logging
import functools

l = logging.getLogger("claripy.backends.backend_vsa")

from .model_backend import ModelBackend, BackendError
from ..vsa import expand_ifproxy, expr_op_expand_ifproxy

def arg_filter(f):
    @functools.wraps(f)
    def filter(*args): #pylint:disable=redefined-builtin
        if type(args[0]) in {int, long}:
            raise BackendError('Unsupported argument type %s' % type(args[0]))
        return f(*args)

    return filter

def normalize_arg_order(f):
    @functools.wraps(f)
    def normalizer(*args):
        if len(args) != 2:
            raise BackendError('Unsupported arguments number %d' % len(args))

        if type(args[0]) not in { StridedInterval, ValueSet }:
            if type(args[1]) not in { StridedInterval, ValueSet }:
                raise BackendError('Unsupported arguments')
            args = [args[1], args[0]]

        return f(*args)

    return normalizer

def normalize_boolean_arg_types(f):
    def convert_bool(a):
        if isinstance(a, BoolResult):
            return a
        if a == True:
            return TrueResult()
        elif a == False:
            return FalseResult()
        else:
            raise BackendError('Unsupported type %s' % type(a))

    @functools.wraps(f)
    def normalizer(*args):
        new_args = [convert_bool(a) for a in args]

        return f(*new_args)

    return normalizer

def convert_bvv_args(f):
    def convert_bvv(a):
        if isinstance(a, BVV):
            return BackendVSA.CreateStridedInterval(to_conv=a)
        return a

    @functools.wraps(f)
    def converter(*args):
        new_args = [convert_bvv(a) for a in args]

        return f(*new_args)

    return converter

def normalize_reversed_arguments(f):
    @functools.wraps(f)
    def normalizer(self, *args, **kwargs):
        arg_reversed = []
        raw_args = []
        for i in xrange(len(args)):
            if isinstance(args[i], A) and type(args[i].model) in {StridedInterval, ValueSet}:
                if args[i].model.reversed:
                    arg_reversed.append(True)
                    raw_args.append(args[i].reversed)
                    continue
            elif isinstance(args[i], A) and args[i].op == 'Reverse':
                # A delayed reverse
                arg_reversed.append(True)
                raw_args.append(args[i].args[0])
                continue

            # It's not reversed
            arg_reversed.append(False)
            raw_args.append(args[i])

        any_reversed_arg = any(arg_reversed)
        for i in xrange(len(raw_args)):
            raw_args[i] = self.convert(raw_args[i])

        ret = f(self, *raw_args, **kwargs)

        variables = set()
        for a in raw_args:
            if type(a) is A:
                variables |= a.variables
            else:
                variables.add(a.name)

        # inner_i = I(args[0]._claripy, ret, variables=variables)
        if any_reversed_arg:
            return ret.reverse()
            #ret = A(args[0]._claripy, 'Reverse', (inner_i,), variables=variables, collapsible=False)

        return ret

    return normalizer

class BackendVSA(ModelBackend):
    def __init__(self):
        ModelBackend.__init__(self)
        # self._make_raw_ops(set(expression_operations) - set(expression_set_operations), op_module=BackendVSA)
        self._make_expr_ops(set(expression_set_operations), op_class=self)
        self._make_raw_ops(set(backend_operations_vsa_compliant), op_module=BackendVSA)

        self._op_raw['StridedInterval'] = BackendVSA.CreateStridedInterval
        self._op_raw['ValueSet'] = ValueSet.__init__
        self._op_raw['AbstractLocation'] = AbstractLocation.__init__
        self._op_raw['Reverse'] = BackendVSA.Reverse
        self._op_expr['If'] = self.If

    def _convert(self, a, result=None):
        if type(a) in { int, long, float, bool, str }:
            return a
        if type(a) is BVV:
            return BackendVSA.CreateStridedInterval(bits=a.bits, to_conv=a)
        if type(a) in { StridedInterval, ValueSet }:
            return a
        if isinstance(a, BoolResult):
            return a
        if isinstance(a, IfProxy):
            return a

        raise NotImplementedError()

    def _eval(self, expr, n, result=None):
        if isinstance(expr, StridedInterval):
            return expr.eval(n)
        elif isinstance(expr, ValueSet):
            results = []

            while len(results) < n:
                results.extend(expr.eval(n - len(results)))

            return results
        elif isinstance(expr, BoolResult):
            return expr.value
        elif isinstance(expr, IfProxy):
            results = set(self._eval(expr.trueexpr, n, result=result))
            if len(results) < n:
                results |= set(self._eval(expr.falseexpr, n - len(results), result=result))
            return list(results)
        else:
            raise BackendError('Unsupported type %s' % type(expr))

    def _min(self, expr, result=None):
        if isinstance(expr, StridedInterval):
            if expr.is_top():
                # TODO: Return
                return StridedInterval.min_int(expr.bits)

            return expr.lower_bound
        else:
            raise BackendError('Unsupported expr type %s' % type(expr))

    def _max(self, expr, result=None):
        assert type(expr) == StridedInterval

        if expr.is_top():
            # TODO:
            return StridedInterval.max_int(expr.bits)

        return expr.upper_bound

    def _solution(self, obj, v, result=None):
        if isinstance(obj, IfProxy):
            ret = self._solution(obj.trueexpr, v, result=result) or \
                self._solution(obj.falseexpr, v, result=result)
            return ret

        if isinstance(obj, BoolResult):
            return v in obj.value
        else:
            raise NotImplementedError()

    @staticmethod
    def has_true(o):
        return BoolResult.has_true(o)

    @staticmethod
    def has_false(o):
        return BoolResult.has_false(o)

    @staticmethod
    def is_true(o):
        return BoolResult.is_true(o)

    @staticmethod
    def is_false(o):
        return BoolResult.is_false(o)

    #
    # Dealing with constraints
    #

    reversed_operations = { }
    reversed_operations['ULT'] = 'UGE'
    reversed_operations['ULE'] = 'UGT'
    reversed_operations['__ne__'] = '__eq__'
    reversed_operations['__eq__'] = '__ne__'

    def cts_simplifier_Extract(self, args, expr):
        '''
        Convert Extract(a, b, If(...)) to If(..., Extract(a, b, ...), Extract(a, b, ...))

        :param args:
        :return:
        '''

        high, low, to_extract = args
        ifproxy = self.cts_simplify(to_extract.op, to_extract.args, to_extract)

        # Create the new ifproxy
        if ifproxy is None:
            # We cannot handle it
            return None

        elif ifproxy.op == 'If':
            new_ifproxy = A(expr._claripy,
                            'If',
                            (
                                ifproxy.args[0],
                                ifproxy._claripy.Extract(high, low, ifproxy.args[1]),
                                ifproxy._claripy.Extract(high, low, ifproxy.args[2])
                            )
            )

        else:
            return expr

        return new_ifproxy

    def cts_simplifier_Concat(self, args, expr):
        '''
        Convert Concat(a, If(...)) to If(..., Concat(a, ...), Concat(a, ...))

        :param args:
        :return:
        '''

        args = [ self.cts_simplify(ex.op, ex.args, ex) for ex in args ]

        ifproxy_conds = set([ a.args[0] for a in args if a.op == 'If' ])

        if len(ifproxy_conds) == 0:
            # No need to simplify!
            return expr

        elif len(ifproxy_conds) > 1:
            # We have more than one condition. Cannot handle it for now!
            return None

        else:
            concat_trueexpr = [ ]
            concat_falseexpr = [ ]

            for a in args:
                if a.op == "If":
                    concat_trueexpr.append(a.args[1])
                    concat_falseexpr.append(a.args[2])
                else:
                    concat_trueexpr.append(a)
                    concat_falseexpr.append(a)

            new_ifproxy = A(expr._claripy,
                            'If',
                            (
                                list(ifproxy_conds)[0],
                                expr._claripy.Concat(*concat_trueexpr),
                                expr._claripy.Concat(*concat_falseexpr)
                            )
            )

            return new_ifproxy

    def cts_simplifier_I(self, args, expr):
        return expr

    def cts_simplifier_If(self, args, expr):
        return expr

    def cts_simplifier_Reverse(self, args, expr):
        # TODO: How should we deal with Reverse in a smart way?

        return expr

    def cts_handler_ULE(self, args):
        """

        :param args:
        :return:
        """

        # TODO: Now we are assuming the lhs is always to target variable. Fix it.

        lhs, rhs = args

        if isinstance(rhs.model, BVV):
            # Convert it into an SI
            rhs = lhs._claripy.SI(to_conv=rhs.model)

        if isinstance(rhs.model, StridedInterval):
            constrained_si = rhs.model.copy()
            constrained_si.lower_bound = constrained_si.min_int(constrained_si.bits) + 1

            return True, [ ( lhs, constrained_si ) ]
        else:
            import ipdb; ipdb.set_trace()

    def cts_handler_UGT(self, args):
        """

        :param args:
        :return:
        """

        lhs, rhs = args

        if isinstance(rhs.model, BVV):
            # Convert it into an SI
            rhs = lhs._claripy.SI(to_conv=rhs.model)

        if isinstance(rhs.model, StridedInterval):
            constrained_si = rhs.model.copy()
            constrained_si.lower_bound = constrained_si.lower_bound + 1
            constrained_si.upper_bound = constrained_si.max_int(constrained_si.bits)

            return True, [( lhs, constrained_si )]
        else:
            import ipdb; ipdb.set_trace()

    def cts_handler_I(self, args):
        a = args[0]

        if a in (False, 0):
            return False, [ ]
        elif isinstance(a, BVV) and a.value == 0:
            return False, [ ]

        return True, [ ]

    def cts_handler_Not(self, args):
        """
        The argument should be False

        :param args:
        :return:
        """

        a = args[0]
        expr_op = a.op
        expr_args = a.args

        # Reverse the op
        expr_op = self.reversed_operations[expr_op]

        return self.cts_handle(expr_op, expr_args)

    def cts_handler_And(self, args):
        """

        :param args:
        :return:
        """

        sat = True
        lst = [ ]

        # Both sides must be true
        for arg in args:
            s, l = self.cts_handle(arg.op, arg.args)

            sat &= s
            lst.extend(l)

        if not sat:
            lst = [ ]

        return sat, lst

    def cts_handler___ne__(self, args):
        return self.cts_handler_eq_ne(args, False)

    def cts_handler___eq__(self, args):
        return self.cts_handler_eq_ne(args, True)

    def cts_handler_eq_ne(self, args, is_eq):
        """

        :param args:
        :return: True or False, and a list of (original_si, constrained_si) tuples
        """

        lhs, rhs = args

        if not isinstance(lhs, A):
            raise ClaripyBackendVSAError('Left-hand-side expression is not an A object.')

        size = lhs.size()

        if type(rhs) in (int, long):
            # Convert it into a BVV
            rhs = I(lhs._claripy, BVV(rhs, size))

        if not isinstance(rhs, A):
            raise ClaripyBackendVSAError('Right-hand-side expression cannot be converted to an A object.')

        sat = True

        # TODO: Make sure the rhs doesn't contain any IfProxy

        lhs = self.cts_simplify(lhs.op, lhs.args, lhs)

        if lhs.op == 'If':
            condition, trueexpr, falseexpr = lhs.args

            if is_eq:
                # __eq__
                take_true = lhs._claripy.is_true(rhs == trueexpr)
                take_false = lhs._claripy.is_true(rhs == falseexpr)
            else:
                # __ne__
                take_true = lhs._claripy.is_true(rhs == falseexpr)
                take_false = lhs._claripy.is_true(rhs == trueexpr)

            if take_true and take_false:
                # It's always satisfiable
                return True, [ ]

            elif take_true:
                # We take the true side
                return self.cts_handle(condition.op, condition.args)

            elif take_false:
                # We take the false side

                # Reverse the operation first
                rev_op = self.reversed_operations[condition.op]

                return self.cts_handle(rev_op, condition.args)

            else:
                # Not satisfiable
                return False, [ ]
        elif isinstance(lhs.model, StridedInterval):
            rhs = lhs._claripy.SI(to_conv=rhs)
            if is_eq:
                return True, [ (lhs, rhs)]
            else:
                if lhs.model.upper_bound <= rhs.model.upper_bound:
                    r = lhs._claripy.SI(bits=rhs.size(),
                                        lower_bound=lhs.model.lower_bound,
                                        upper_bound=rhs.model.lower_bound - 1)

                    return True, [ (lhs, r) ]
                elif lhs.model.lower_bound >= rhs.model.lower_bound:
                    r = lhs._claripy.SI(bits=rhs.size(),
                                        lower_bound=rhs.model.lower_bound + 1,
                                        upper_bound=lhs.model.upper_bound)

                    return True, [ (lhs, r) ]
                else:
                    # We cannot handle it precisely
                    return True, [ ]
        else:
            import ipdb; ipdb.set_trace()

    def cts_simplify(self, op, args, expr):
        return getattr(self, "cts_simplifier_%s" % op)(args, expr)

    def cts_handle(self, op, args):
        return getattr(self, "cts_handler_%s" % op)(args)

    def constraint_to_si(self, expr):
        """
        We take in constraints, and convert them into constrained strided-intervals.

        For example, expr =
        <A __ne__ (
                    <A Extract (0,
                                0,
                                <A Concat (<A BVV(0x0, 63)>,
                                            <A If (
                                                    <A ULE (<A SI_1208<64>0x1[0x0, 0x100]>, <A BVV(0x27, 64)>)>,
                                                    <A BVV(0x1, 1)>,
                                                    <A BVV(0x0, 1)>
                                            )>
                                )>
                    )>,
                    0
        )>
        The result would be
        [ ( SI_1208<64>0x1[0x0, 0x100], SI_XXXX<64>0x1[0x0, 0x27] ) ]

        As we can only deal with bits, we will convert all integers into BVV during the solving and conversion process.

        :param expr: The constraint
        :return: whether the expr is satisfiable (boolean), and a list of tuples in form of
                (original_si, constrained_si).
        """

        sat, lst = self.cts_handle(expr.op, expr.args)

        return sat, lst

    #
    # Backend Operations
    #

    def _identical(self, a, b, result=None):
        return BackendVSA.is_true(a == b)

    def _unique(self, obj, result=None):
        if isinstance(obj, StridedInterval):
            return obj.unique
        elif isinstance(obj, ValueSet):
            return obj.unique
        elif isinstance(obj, IfProxy):
            return False
        else:
            raise BackendError('Not supported type of operand %s' % type(obj))

    @staticmethod
    @expand_ifproxy
    @normalize_boolean_arg_types
    def And(a, b):
        return a & b

    @staticmethod
    @expand_ifproxy
    @normalize_boolean_arg_types
    def Not(a):
        return ~a

    @staticmethod
    @normalize_arg_order
    def ULT(a, b):
        return a < b

    def If(self, cond, true_expr, false_expr, result=None): #pylint:disable=unused-argument
        exprs = []
        cond_model = self.convert(cond)
        if self.has_true(cond_model):
            exprs.append(true_expr)
        if self.has_false(cond_model):
            exprs.append(false_expr)

        if len(exprs) == 1:
            expr = self.convert(exprs[0])
        else:
            # TODO: How to handle it?
            expr = IfProxy(cond, self.convert(exprs[0]), self.convert(exprs[1]))

        return expr

    # TODO: Implement other operations!

    @staticmethod
    @expand_ifproxy
    def LShR(expr, shift_amount):
        return expr >> shift_amount

    @staticmethod
    @expand_ifproxy
    def Concat(*args):
        ret = None
        for expr in args:
            assert type(expr) in { StridedInterval, ValueSet, BVV }
            if type(expr) is BVV:
                expr = BackendVSA.CreateStridedInterval(bits=expr.bits, to_conv=expr)

            ret = ret.concat(expr) if ret is not None else expr

        return ret

    @arg_filter
    def _size(self, arg, result=None):
        if type(arg) in { StridedInterval, ValueSet, IfProxy }:
            return len(arg)
        else:
            return arg.size()

    @staticmethod
    @expand_ifproxy
    def Extract(*args):
        low_bit = args[1]
        high_bit = args[0]
        expr = args[2]

        assert type(expr) in { StridedInterval, ValueSet }

        ret = expr.extract(high_bit, low_bit)

        return ret

    @staticmethod
    @expand_ifproxy
    @convert_bvv_args
    def SignExt(*args):
        new_bits = args[0]
        expr = args[1]

        assert type(expr) is StridedInterval
        # TODO: Use sign_extend instead
        return expr.zero_extend(new_bits + expr.bits)

    @staticmethod
    @expand_ifproxy
    @convert_bvv_args
    def ZeroExt(*args):
        new_bits = args[0]
        expr = args[1]

        assert type(expr) is StridedInterval
        return expr.zero_extend(new_bits + expr.bits)

    @staticmethod
    @expand_ifproxy
    def Reverse(arg):
        assert type(arg) in {StridedInterval, ValueSet}

        return arg.reverse()

    @expr_op_expand_ifproxy
    @normalize_reversed_arguments
    def union(self, *args, **kwargs): #pylint:disable=unused-argument,no-self-use
        if len(args) != 2:
            raise BackendError('Incorrect number of arguments (%d) passed to BackendVSA.union().' % len(args))

        ret = args[0].union(args[1])

        if ret is NotImplemented:
            ret = args[1].union(args[0])

        return ret

    @expr_op_expand_ifproxy
    @normalize_reversed_arguments
    def intersection(self, *args, **kwargs): #pylint:disable=unused-argument,no-self-use
        if len(args) != 2:
            raise BackendError('Incorrect number of arguments (%d) passed to BackendVSA.intersection().' % len(args))

        ret = None

        for arg in args:
            if ret is None:
                ret = arg
            else:
                ret = ret.intersection(arg)

        return ret

    @expr_op_expand_ifproxy
    @normalize_reversed_arguments
    def widen(self, *args, **kwargs): #pylint:disable=unused-argument,no-self-use
        if len(args) != 2:
            raise BackendError('Incorrect number of arguments (%d) passed to BackendVSA.widen().' % len(args))

        return args[0].widen(args[1])

    @staticmethod
    def CreateStridedInterval(name=None, bits=0, stride=None, lower_bound=None, upper_bound=None, to_conv=None):
        '''

        :param name:
        :param bits:
        :param stride:
        :param lower_bound:
        :param upper_bound:
        :param to_conv:
        :return:
        '''
        if to_conv is not None:
            if isinstance(to_conv, A):
                to_conv = to_conv.model
            if type(to_conv) is StridedInterval:
                # No conversion will be done
                return to_conv

            if type(to_conv) not in {int, long, BVV}:
                raise BackendError('Unsupported to_conv type %s' % type(to_conv))

            if stride is not None or lower_bound is not None or \
                            upper_bound is not None:
                raise BackendError('You cannot specify both to_conv and other parameters at the same time.')

            if type(to_conv) is BVV:
                bits = to_conv.bits
                to_conv_value = to_conv.value
            else:
                bits = bits
                to_conv_value = to_conv

            stride = 0
            lower_bound = to_conv_value
            upper_bound = to_conv_value

        bi = StridedInterval(name=name,
                             bits=bits,
                             stride=stride,
                             lower_bound=lower_bound,
                             upper_bound=upper_bound)
        return bi

    @staticmethod
    def CreateTopStridedInterval(bits, name=None, signed=False): #pylint:disable=unused-argument,no-self-use
        return StridedInterval.top(bits, name=None, signed=signed)

from ..bv import BVV
from ..ast import A, I
from ..operations import backend_operations_vsa_compliant, expression_set_operations
from ..vsa import StridedInterval, ValueSet, AbstractLocation, BoolResult, TrueResult, FalseResult
from ..vsa import IfProxy
from ..errors import ClaripyBackendVSAError
