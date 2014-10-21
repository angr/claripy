import logging
import functools

l = logging.getLogger("claripy.backends.backend_vsa")

from .model_backend import ModelBackend, BackendError
from ..vsa import expand_ifproxy

def arg_filter(f):
    @functools.wraps(f)
    def filter(*args):
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
        self._op_raw['size'] = BackendVSA.size
        self._op_raw['Reverse'] = BackendVSA.Reverse
        self._op_raw['Identical'] = BackendVSA.Identical
        self._op_raw['name'] = BackendVSA.name
        self._op_expr['If'] = self.If

    def add_exprs(self, solver, constraints):
        pass

    def results_exprs(self, solver, extra_constraints, generic_backend):
        return Result(True, self)

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

        import ipdb; ipdb.set_trace()
        raise NotImplementedError()

    def eval(self, expr, n, result=None):
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
            results = set(self.eval(expr.trueexpr, n, result=result))
            if len(results) < n:
                results |= set(self.eval(expr.falseexpr, n - len(results), result=result))
            return list(results)
        else:
            raise BackendError('Unsupported type %s' % type(expr))

    def min(self, expr, result=None):
        if isinstance(expr, StridedInterval):
            if expr.is_top():
                # TODO: Return
                return StridedInterval.min_int(expr.bits)

            return expr.lower_bound
        else:
            raise BackendError('Unsupported expr type %s' % type(expr))

    def max(self, expr, result=None):
        assert type(expr) == StridedInterval

        if expr.is_top():
            # TODO:
            return StridedInterval.max_int(expr.bits)

        return expr.upper_bound

    def solution(self, obj, v, result=None):
        if isinstance(obj, IfProxy):
            ret = self.solution(obj.trueexpr, v, result=result) or \
                self.solution(obj.falseexpr, v, result=result)
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

    def constraint_to_si(self, expr):
        def _find_target_expr(m):
            expr_ = None
            if isinstance(m, A):
                if m.op in ['Extract', 'ZeroExt']:
                    expr_ = _find_target_expr(m.args[-1])
                    if expr_ is None:
                        return m.args[-1]
                    else:
                        return expr_

            return None

        if not isinstance(expr.model, IfProxy):
            return None, None

        ifproxy = expr.model
        condition = ifproxy.condition
        condition_ast = condition
        op = condition_ast.op

        if op == 'ULT':
            left_expr = condition_ast.args[0]
            right_expr = condition_ast.args[1]
            if type(right_expr.model) in {BVV}:
                # import ipdb; ipdb.set_trace()
                target_expr = _find_target_expr(left_expr)
                if target_expr is None:
                    return None
                pivoted = condition_ast.pivot(left=target_expr)
                right_expr = pivoted.args[1]
                left_expr = pivoted.args[0]
            # Convert them to SI
            # si_left = BackendVSA.CreateStridedInterval(bits=left.bits, to_conv=left)
            si_right = BackendVSA.CreateStridedInterval(bits=right_expr.model.bits, to_conv=right_expr.model)
            # Modify the lower bound
            si_right.lower_bound = StridedInterval.min_int(si_right.bits)
            si_right.stride = left_expr.model.stride

            return left_expr, si_right
        else:
            # FIXME: Finish it!
            # import ipdb; ipdb.set_trace()

            return None, None

    #
    # Backend Operations
    #

    @staticmethod
    def Identical(a, b):
        return BackendVSA.is_true(a == b)
    identical = Identical

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

    def If(self, cond, true_expr, false_expr, result=None):
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
    def Concat(*args):
        ret = None
        for expr in args:
            assert type(expr) in { StridedInterval, ValueSet, BVV }
            if type(expr) is BVV:
                expr = BackendVSA.CreateStridedInterval(bits=expr.bits, to_conv=expr)

            ret = ret.concat(expr) if ret is not None else expr

        return ret

    @staticmethod
    @arg_filter
    def size(arg):
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
        assert type(arg) in { StridedInterval, ValueSet }

        return arg.reverse()

    @staticmethod
    @expand_ifproxy
    def Reverse(arg):
        assert type(arg) in {StridedInterval, ValueSet}

        return arg.reverse()

    @normalize_reversed_arguments
    def union(self, *args, **kwargs):
        assert len(args) == 2

        ret = args[0].union(args[1])

        return ret

    @normalize_reversed_arguments
    def intersection(self, *args, **kwargs):
        ret = None

        for arg in args:
            if ret is None:
                ret = arg
            else:
                ret = ret.intersection(arg)

        return ret

    @normalize_reversed_arguments
    def widen(self, *args, **kwargs):
        assert len(args) == 2

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
                import ipdb; ipdb.set_trace()
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
    def CreateTopStridedInterval(bits, signed=False):
        return StridedInterval.top(bits, signed=signed)

from ..bv import BVV
from ..ast import A, I
from ..operations import backend_operations_vsa_compliant, backend_vsa_creation_operations, expression_operations, expression_set_operations
from ..vsa import StridedInterval, ValueSet, AbstractLocation, BoolResult, TrueResult, FalseResult
from ..result import Result
from ..vsa import IfProxy