import logging
import functools

l = logging.getLogger("claripy.backends.backend_vsa")

from ..backend import Backend, BackendError
from ..vsa import expand_ifproxy, expr_op_expand_ifproxy

def arg_filter(f):
    @functools.wraps(f)
    def filter(*args): #pylint:disable=redefined-builtin
        if type(args[0]) in {int, long}: #pylint:disable=unidiomatic-typecheck
            raise BackendError('Unsupported argument type %s' % type(args[0]))
        return f(*args)

    return filter

def normalize_arg_order(f):
    @functools.wraps(f)
    def normalizer(*args):
        if len(args) != 2:
            raise BackendError('Unsupported arguments number %d' % len(args))

        if type(args[0]) not in { StridedInterval, DiscreteStridedIntervalSet, ValueSet }: #pylint:disable=unidiomatic-typecheck
            if type(args[1]) not in { StridedInterval, DiscreteStridedIntervalSet, ValueSet }: #pylint:disable=unidiomatic-typecheck
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
            if isinstance(args[i], Base) and \
                            type(args[i].model) in { #pylint:disable=unidiomatic-typecheck
                                                    StridedInterval,
                                                    DiscreteStridedIntervalSet,
                                                    ValueSet
            }:
                if args[i].model.reversed:
                    arg_reversed.append(True)
                    raw_args.append(args[i].reversed)
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
            if isinstance(a, Base):
                variables |= a.variables
            else:
                variables.add(a.name)

        # inner_i = I(args[0]._claripy, ret, variables=variables)
        if any_reversed_arg:
            return ret.reverse()
            #ret = A(args[0]._claripy, 'Reverse', (inner_i,), variables=variables, collapsible=False)

        return ret

    return normalizer

class BackendVSA(Backend):
    def __init__(self):
        Backend.__init__(self)
        # self._make_raw_ops(set(expression_operations) - set(expression_set_operations), op_module=BackendVSA)
        self._make_expr_ops(set(expression_set_operations), op_class=self)
        self._make_raw_ops(set(backend_operations_vsa_compliant), op_module=BackendVSA)

        self._op_raw['StridedInterval'] = BackendVSA.CreateStridedInterval
        self._op_raw['ValueSet'] = ValueSet.__init__
        self._op_raw['AbstractLocation'] = AbstractLocation.__init__
        self._op_raw['Reverse'] = BackendVSA.Reverse
        self._op_expr['If'] = self.If

    def _convert(self, a, result=None):
        if type(a) in { int, long, float, bool, str }: #pylint:disable=unidiomatic-typecheck
            return a
        if type(a) is BVV: #pylint:disable=unidiomatic-typecheck
            return BackendVSA.CreateStridedInterval(bits=a.bits, to_conv=a)
        if type(a) in { StridedInterval, DiscreteStridedIntervalSet, ValueSet }: #pylint:disable=unidiomatic-typecheck
            return a
        if isinstance(a, BoolResult):
            return a
        if isinstance(a, IfProxy):
            return a

        raise BackendError("why is fish raising NotImplementedError INSTEAD OF THE ERROR THAT'S SUPPOSED TO BE RAISED IN THIS SITUATION? SERIOUSLY, JUST RAISE A BACKENDERROR AND EVERYONE WILL BE HAPPY, BUT NO, PEOPLE HAVE TO RAISE THEIR OWN ERRORS INSTEAD OF USING THE ERRORS THAT WERE ****DESIGNED**** FOR THIS SORT OF THING. WHY DO I BOTHER DESIGNING A GOOD ERROR HIERARCHY, ANYWAYS? WILL IT BE USED? NO! IT'LL BE ALL NotImplementedError('THIS') or Exception('THAT') AND EVERYTHING WILL MELT DOWN. UGH!")

    def _eval(self, expr, n, result=None, solver=None, extra_constraints=()):
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

    def _min(self, expr, result=None, solver=None, extra_constraints=()):
        if isinstance(expr, IfProxy):
            v1 = self.min(expr.trueexpr)
            v2 = self.min(expr.falseexpr)

            return min(v1, v2)

        elif isinstance(expr, StridedInterval):
            if expr.is_top:
                # TODO: Return
                return StridedInterval.min_int(expr.bits)

            return expr.lower_bound
        else:
            raise BackendError('Unsupported expr type %s' % type(expr))

    def _max(self, expr, result=None, solver=None, extra_constraints=()):
        if isinstance(expr, IfProxy):
            v1 = self.max(expr.trueexpr)
            v2 = self.max(expr.falseexpr)

            return max(v1, v2)

        else:
            if isinstance(expr, StridedInterval):
                if expr.is_top:
                    # TODO:
                    return StridedInterval.max_int(expr.bits)

                return expr.upper_bound

            else:
                raise BackendError('Unsupported expr type %s' % type(expr))

    def _solution(self, obj, v, result=None, solver=None, extra_constraints=()):
        if isinstance(obj, IfProxy):
            ret = self._solution(obj.trueexpr, v, result=result) or \
                self._solution(obj.falseexpr, v, result=result)
            return ret

        if isinstance(obj, BoolResult):
            return v in obj.value

        if isinstance(obj, StridedInterval):
            return not obj.intersection(v).is_empty

        if isinstance(obj, ValueSet):
            for _, si in obj.items():
                if not si.intersection(v).is_empty:
                    return True
            return False

        raise NotImplementedError(type(obj).__name__)

    def _has_true(self, o):
        return BoolResult.has_true(o)

    def _has_false(self, o):
        return BoolResult.has_false(o)

    def _is_true(self, o):
        return BoolResult.is_true(o)

    def _is_false(self, o):
        return BoolResult.is_false(o)

    #
    # Dealing with constraints
    #

    reversed_operations = { }
    reversed_operations['__ne__'] = '__eq__'
    reversed_operations['__eq__'] = '__ne__'
    reversed_operations['ULT'] = 'UGE'
    reversed_operations['UGT'] = 'ULE'
    reversed_operations['ULE'] = 'UGT'
    reversed_operations['UGE'] = 'ULT'
    reversed_operations['SLT'] = 'SGE'
    reversed_operations['SLE'] = 'SGT'
    reversed_operations['SGT'] = 'SLE'
    reversed_operations['SGE'] = 'SLT'
    reversed_operations['__le__'] = '__gt__'
    reversed_operations['__lt__'] = '__ge__'
    reversed_operations['__ge__'] = '__lt__'
    reversed_operations['__gt__'] = '__le__'

    comparison_info = { }
    # Tuples look like (is_lt, is_eq, is_unsigned)
    comparison_info['SLT'] = (True, False, False)
    comparison_info['SLE'] = (True, True, False)
    comparison_info['SGT'] = (False, False, False)
    comparison_info['SGE'] = (False, True, False)
    comparison_info['ULT'] = (True, False, True)
    comparison_info['ULE'] = (True, True, True)
    comparison_info['UGT'] = (False, False, True)
    comparison_info['UGE'] = (False, True, True)
    comparison_info['__lt__'] = comparison_info['ULT']
    comparison_info['__le__'] = comparison_info['ULE']
    comparison_info['__gt__'] = comparison_info['UGT']
    comparison_info['__ge__'] = comparison_info['UGE']

    def cts_simplifier_ZeroExt(self, args, expr, condition):
        """
        :param args:
        :param expr:
        :return: (new ast, new condition)
        """
        cond_op, cond_arg = condition
        # Normalize cond_arg
        if type(cond_arg) in (int, long): #pylint:disable=unidiomatic-typecheck
            cond_arg = _all_operations.BVV(cond_arg, expr.size())

        extended_bits, arg = args

        if cond_arg.size() <= arg.size() or \
                _all_operations.is_true(cond_arg[ expr.size() - 1 : expr.size() - extended_bits ] == 0):
            # We can safely eliminate this layer of ZeroExt
            if cond_arg.size() < arg.size():
                larger_cond_arg = cond_arg.zero_extend(arg.size() - cond_arg.size())
                if not isinstance(larger_cond_arg.model, Base):
                    return self.cts_simplify(arg.op, arg.args, arg, (cond_op, larger_cond_arg))
            else:
                return self.cts_simplify(arg.op, arg.args, arg, (cond_op, cond_arg[ arg.size() - 1 : 0 ]))

        else:
            # TODO: We may also handle the '__eq__' and '__ne__' case
            #__import__('ipdb').set_trace()
            # We cannot handle this...
            return expr, condition

    def cts_simplifier_SignExt(self, args, expr, condition):
        """

        :param args:
        :param expr:
        :param condition:
        :return:
        """
        # TODO: Review the logic of this method
        cond_op, cond_arg = condition
        # Normalize them
        if type(cond_arg) in (int, long): #pylint:disable=unidiomatic-typecheck
            cond_arg = _all_operations.BVV(cond_arg, expr.size())

        extended_bits, arg = args

        if cond_arg.size() <= arg.size() or \
                _all_operations.is_true(cond_arg[expr.size() - 1: expr.size() - extended_bits] == 0):
            # We can safely eliminate this layer of SignExt
            if cond_arg.size() < arg.size():
                larger_cond_arg = cond_arg.zero_extend(arg.size() - cond_arg.size()).resolved()
                if not isinstance(larger_cond_arg, Base):
                    return self.cts_simplify(arg.op, arg.args, arg, (cond_op, larger_cond_arg))
            else:
                return self.cts_simplify(arg.op, arg.args, arg, (cond_op, cond_arg[arg.size() - 1: 0]))

        else:
            # TODO: We may also handle the '__eq__' and '__ne__' case
            # __import__('ipdb').set_trace()
            # We cannot handle this...
            return expr, condition

    def cts_simplifier_Extract(self, args, expr, condition):
        '''
        Convert Extract(a, b, If(...)) to If(..., Extract(a, b, ...), Extract(a, b, ...))

        :param args:
        :return:
        '''

        high, low, to_extract = args
        ast, cond = self.cts_simplify(to_extract.op, to_extract.args, to_extract, condition)

        # Create the new ifproxy
        if ast is None:
            # We cannot handle it
            return None, condition

        elif ast.op == 'If':
            new_ifproxy = _all_operations.If(
                                ast.args[0],
                                _all_operations.Extract(high, low, ast.args[1]),
                                _all_operations.Extract(high, low, ast.args[2])
                            )

        else:
            cond_op, cond_arg = cond
            if type(cond_arg.model) in (int, long): #pylint:disable=unidiomatic-typecheck
                cond_arg = _all_operations.BVV(cond_arg, ast.size())
            elif type(cond_arg.model) in (StridedInterval, DiscreteStridedIntervalSet, BVV): #pylint:disable=unidiomatic-typecheck
                if ast.size() > cond_arg.size():
                    # Make sure two operands have the same size
                    cond_arg = _all_operations.ZeroExt(ast.size() - cond_arg.size(), cond_arg)

            if cond_arg.size() - 1 < high + 1 or \
                    _all_operations.is_true(cond_arg[cond_arg.size() - 1 : high + 1] == 0):
                # The upper part doesn't matter
                # We can handle it
                return self.cts_simplify(ast.op, ast.args, ast, (cond_op, cond_arg))
            else:
                # We cannot further simplify it
                return expr, condition

        return new_ifproxy, condition

    def cts_simplifier_Concat(self, args, expr, condition):
        '''
        Convert Concat(a, If(...)) to If(..., Concat(a, ...), Concat(a, ...))

        :param args:
        :return:
        '''

        new_args = [ self.cts_simplify(ex.op, ex.args, ex, condition) for ex in args ]

        ifproxy_conds = set([ a.args[0] for a, new_cond in new_args if a.op == 'If' ])

        if len(ifproxy_conds) == 0:
            # Let's check if we can remove this layer of Concat
            cond = condition[1]
            if len(args) == 2:
                if cond.size() - 1 >= cond.size() - args[0].size():
                    if _all_operations.is_true(args[0] == cond[ cond.size() - 1 : cond.size() - args[0].size() ]):
                        # Yes! We can remove it!
                        # TODO: This is hackish...
                        new_cond = (condition[0], cond[ cond.size() - args[0].size() - 1 : 0])
                        return self.cts_simplify(args[1].op, args[1].args, args[1], new_cond)

                else:
                    # args[0].size() == 0? It must be a bug.
                    raise ClaripyBackendVSAError(
                        'args[0].size() == %d (args[0] is \'%s\'). Please report this bug.' % (args[0].size, str(args[0])))

            # Cannot simplify it anymore
            return expr, condition

        elif len(ifproxy_conds) > 1:
            # We have more than one condition. Cannot handle it for now!
            return None, condition

        else:
            concat_trueexpr = [ ]
            concat_falseexpr = [ ]

            all_new_conds = set([ new_cond for a, new_cond in new_args ])

            if len(all_new_conds) > 1:
                # New conditions are not consistent. Can't handle it.
                return expr, condition

            for a, new_cond in new_args:
                if a.op == "If":
                    concat_trueexpr.append(a.args[1])
                    concat_falseexpr.append(a.args[2])
                else:
                    concat_trueexpr.append(a)
                    concat_falseexpr.append(a)

            new_ifproxy = _all_operations.If(
                                list(ifproxy_conds)[0],
                                _all_operations.Concat(*concat_trueexpr),
                                _all_operations.Concat(*concat_falseexpr)
                            )

            return new_ifproxy, condition

    def cts_simplifier_I(self, args, expr, condition): #pylint:disable=unused-argument,no-self-use
        return expr, condition

    def cts_simplifier_If(self, args, expr, condition): #pylint:disable=unused-argument,no-self-use
        return expr, condition

    def cts_simplifier_Reverse(self, args, expr, condition): #pylint:disable=unused-argument
        # TODO: How should we deal with Reverse in a smart way?

        arg = args[0]

        return self.cts_simplify(arg.op, arg.args, arg, condition)

    def cts_simplifier_widen(self, args, expr, condition): #pylint:disable=unused-argument,no-self-use

        return expr, condition

    def cts_simplifier_intersection(self, args, expr, condition): #pylint:disable=unused-argument,no-self-use

        return expr, condition

    def cts_simplifier___or__(self, args, expr, condition):
        claripy = expr._claripy
        argl, argr = args
        if argl is argr or claripy.is_true(argl == argr):
            return self.cts_simplify(argl.op, argl.args, argl, condition)
        elif claripy.is_true(argl == 0):
            return self.cts_simplify(argr.op, argr.args, argr, condition)
        elif claripy.is_true(argr == 0):
            return self.cts_simplify(argl.op, argl.args, argl, condition)
        else:
            return expr, condition

    def cts_simplifier___and__(self, args, expr, condition):

        argl, argr = args
        if argl is argr:
            # Operands are the same one!
            # We can safely remove this layer of __and__
            return self.cts_simplify(argl.op, argl.args, argl, condition)

        elif argl.structurally_match(argr):
            # Operands are the same
            # Safely remove the __and__ operation
            return self.cts_simplify(argl.op, argl.args, argl, condition)

        else:
            # We cannot handle it
            return expr, condition

    def cts_simplifier___xor__(self, args, expr, condition):
        argl, argr = args

        if _all_operations.is_true(argl == 0):
            # :-)
            return self.cts_simplify(argr.op, argr.args, argr, condition)
        elif _all_operations.is_true(argr == 0):
            # :-)
            return self.cts_simplify(argl.op, argl.args, argl, condition)
        else:
            # :-(
            return expr, condition

    def cts_simplifier___add__(self, args, expr, condition):

        argl, argr = args
        if _all_operations.is_true(argr == 0):
            # This layer of __add__ can be removed
            return self.cts_simplify(argl.op, argl.args, argl, condition)
        elif _all_operations.is_true(argl == 0):
            # This layer of __add__ can be removed
            return self.cts_simplify(argr.op, argr.args, argr, condition)
        else:

            if isinstance(argl.model, BVV):
                new_cond = (condition[0], condition[1] - argl)
                return self.cts_simplify(argr.op, argr.args, argr, new_cond)

            elif isinstance(argr.model, BVV):
                new_cond = (condition[0], condition[1] - argr)
                return self.cts_simplify(argl.op, argl.args, argl, new_cond)

            else:
                return expr, condition

    def cts_simplifier___radd__(self, args, expr, condition):
        return self.cts_simplifier___add__((args[1], args[0]), expr, condition)

    def cts_simplifier___sub__(self, args, expr, condition):
        """

        :param args:
        :param expr:
        :param condition:
        :return:
        """

        argl, argr = args
        if _all_operations.is_true(argr == 0):
            return self.cts_simplify(argl.op, argl.args, argl, condition)
        elif _all_operations.is_true(argl == 0):
            return self.cts_simplify(argr.op, argr.args, argr, condition)
        else:
            #__import__('ipdb').set_trace()
            return expr, condition

    def cts_simplifier___rsub__(self, args, expr, condition):
        return self.cts_simplifier___sub__((args[1], args[0]), expr, condition)

    def cts_simplifier___rshift__(self, args, expr, condition):

        arg, offset = args
        if _all_operations.is_true(offset == 0):
            return self.cts_simplify(arg.op, arg.args, arg, condition)
        else:
            return expr, condition

    def cts_simplifier___lshift__(self, args, expr, condition):

        arg, offset = args
        if _all_operations.is_true(offset == 0):
            return self.cts_simplify(arg.op, arg.args, arg, condition)
        else:
            return expr, condition

    def cts_simplifier___invert__(self, args, expr, condition):

        arg = args[0]
        if arg.op == 'If':
            new_arg = _all_operations.If(args[0], args[1].__invert__(), args[2].__invert__())

            return self.cts_simplify(new_arg.op, new_arg.args, expr, condition)

        else:
            __import__('ipdb').set_trace()
            return expr, condition

    def cts_simplifier_union(self, args, expr, condition): #pylint:disable=unused-argument,no-self-use

        return expr, condition

    def cts_simplifier___mod__(self, args, expr, condition): #pylint:disable=unused-argument,no-self-use

        return expr, condition

    def cts_simplifier___div__(self, args, expr, condition): #pylint:disable=unused-argument,no-self-use

        return expr, condition

    def cts_simplifier___eq__(self, args, expr, condition): #pylint:disable=unused-argument,no-self-use

        l.error('cts_simplifier___eq__() should not exist. This is just a workaround for VSA. Fish will fix the issue later.')

        return expr, condition

    def cts_handler_comparison(self, args, comp=None):
        """
        Handles all comparisons.
        :param args:
        :param comp:
        :return:
        """

        if comp in self.comparison_info:
            is_lt, is_equal, is_unsigned = self.comparison_info[comp]
        else:
            raise ClaripyBackendVSAError('Support for comparison %s is not implemented. Please report it.' % comp)

        lhs, rhs = args

        if not isinstance(lhs, Base):
            raise ClaripyBackendVSAError('Left-hand-side expression is not an AST object.')

        # Maybe the target variable is the rhs
        if isinstance(lhs.model, BVV):
            new_op = self.reversed_operations[comp]
            new_lhs, new_rhs = rhs, lhs
            return self.cts_handle(new_op, (new_lhs, new_rhs))

        if type(rhs) in (int, long) or type(rhs.model) is BVV: #pylint:disable=unidiomatic-typecheck
            # Convert it into an SI
            rhs = _all_operations.SI(to_conv=rhs)

        if not isinstance(rhs, Base):
            raise ClaripyBackendVSAError('Right-hand-side expression cannot be converted to an AST object.')

        if lhs.op == 'If':
            condition, trueexpr, falseexpr = lhs.args

            if is_unsigned:
                if is_lt:
                    if is_equal:
                        take_true = _all_operations.is_true(trueexpr.ULE(rhs))
                        take_false = _all_operations.is_true(falseexpr.ULE(rhs))
                    else:
                        take_true = _all_operations.is_true(falseexpr.ULT(rhs))
                        take_false = _all_operations.is_true(trueexpr.ULT(rhs))
                else:
                    if is_equal:
                        take_true = _all_operations.is_true(trueexpr.UGE(rhs))
                        take_false = _all_operations.is_true(falseexpr.UGE(rhs))
                    else:
                        take_true = _all_operations.is_true(trueexpr.UGT(rhs))
                        take_false = _all_operations.is_true(falseexpr.UGT(rhs))
            else:
                if is_lt:
                    if is_equal:
                        take_true = _all_operations.is_true(trueexpr <= rhs)
                        take_false = _all_operations.is_true(falseexpr <= rhs)
                    else:
                        take_true = _all_operations.is_true(trueexpr < rhs)
                        take_false = _all_operations.is_true(falseexpr < rhs)
                else:
                    if is_equal:
                        take_true = _all_operations.is_true(trueexpr >= rhs)
                        take_false = _all_operations.is_true(falseexpr >= rhs)
                    else:
                        take_true = _all_operations.is_true(trueexpr > rhs)
                        take_false = _all_operations.is_true(falseexpr > rhs)

            if take_true and take_false:
                # It's always satisfiable
                return True, [ ]
            elif take_true:
                return self.cts_handle(condition.op, condition.args)
            elif take_false:
                rev_op = self.reversed_operations[condition.op]
                return self.cts_handle(rev_op, condition.args)
            else:
                # Not satisfiable
                return False, [ ]

        elif isinstance(rhs.model, StridedInterval) and isinstance(lhs.model, StridedInterval):
            if isinstance(lhs.model, Base):
                # It cannot be computed by our backend...
                # We just give up for now
                return True, [ ]

            stride = lhs.model.stride

            if is_lt:
                # < or <=
                if is_unsigned: lb = 0
                else: lb = StridedInterval.min_int(rhs.length)

                ub = rhs.model.upper_bound
                if not is_equal:
                    # <
                    ub = ub - 1

            else:
                # > or >=
                if is_unsigned: ub = StridedInterval.max_int(rhs.length)
                else: ub = StridedInterval.max_int(rhs.model.bits - 1)

                lb = rhs.model.lower_bound
                if not is_equal:
                    # >
                    lb = lb + 1

            if stride == 0 and lb != ub:
                # Make sure the final StridedInterval is always meaningful. See issue #55.
                stride = 1

            si_replacement = _all_operations.SI(bits=rhs.length, stride=stride, lower_bound=lb, upper_bound=ub)
            return True, [(lhs, si_replacement)]

        else:
            return True, [ ]

    def cts_handler___lt__(self, args): return self.cts_handler_comparison(args, comp='__lt__')
    def cts_handler___le__(self, args): return self.cts_handler_comparison(args, comp='__le__')
    def cts_handler___gt__(self, args): return self.cts_handler_comparison(args, comp='__gt__')
    def cts_handler___ge__(self, args): return self.cts_handler_comparison(args, comp='__ge__')
    def cts_handler_ULT(self, args): return self.cts_handler_comparison(args, comp='ULT')
    def cts_handler_ULE(self, args): return self.cts_handler_comparison(args, comp='ULE')
    def cts_handler_UGT(self, args): return self.cts_handler_comparison(args, comp='UGT')
    def cts_handler_UGE(self, args): return self.cts_handler_comparison(args, comp='UGE')
    def cts_handler_SLT(self, args): return self.cts_handler_comparison(args, comp='SLT')
    def cts_handler_SLE(self, args): return self.cts_handler_comparison(args, comp='SLE')
    def cts_handler_SGT(self, args): return self.cts_handler_comparison(args, comp='SGT')
    def cts_handler_SGE(self, args): return self.cts_handler_comparison(args, comp='SGE')

    def cts_handler_I(self, args): #pylint:disable=no-self-use
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
            sat_, lst_ = self.cts_handle(arg.op, arg.args)

            sat &= sat_
            lst.extend(lst_)

        if not sat:
            lst = [ ]

        return sat, lst

    def cts_handler_Or(self, args):

        if len(args) == 1:
            return self.cts_handle(args[0].op, args[0].args)

        else:
            if len(args) > 0:
                args = [ self.cts_handle(a.op, a.args) for a in args ]
                if any([not _all_operations.is_false(a) for a in args]):
                    return True, [ ]

                else:
                    return False, [ ]
            return True, [ ]

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

        if not isinstance(lhs, Base):
            raise ClaripyBackendVSAError('Left-hand-side expression is not an AST object.')

        size = lhs.size()

        if type(rhs) in (int, long): #pylint:disable=unidiomatic-typecheck
            # Convert it into a BVV
            rhs = _all_operations.BVV(rhs, size)

        if not isinstance(rhs, Base):
            raise ClaripyBackendVSAError('Right-hand-side expression cannot be converted to an AST object.')

        # TODO: Make sure the rhs doesn't contain any IfProxy

        if lhs.op == 'If':
            condition, trueexpr, falseexpr = lhs.args

            if is_eq:
                # __eq__
                take_true = _all_operations.is_true(rhs == trueexpr)
                take_false = _all_operations.is_true(rhs == falseexpr)
            else:
                # __ne__
                take_true = _all_operations.is_true(rhs == falseexpr)
                take_false = _all_operations.is_true(rhs == trueexpr)

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
        elif isinstance(lhs.model, StridedInterval) or isinstance(lhs.model, BVV):
            if not isinstance(lhs.model, StridedInterval):
                try: lhs = _all_operations.SI(to_conv=lhs)
                except BackendError: return True, [ ] # We cannot convert it to a StridedInterval

            try: rhs = _all_operations.SI(to_conv=rhs)
            except BackendError: return True, [ ]

            if is_eq:
                return True, [ (lhs, rhs)]
            else:
                if lhs.model.upper_bound <= rhs.model.upper_bound:
                    r = _all_operations.SI(bits=rhs.size(),
                                    stride=lhs.model.stride,
                                    lower_bound=lhs.model.lower_bound,
                                    upper_bound=rhs.model.lower_bound - 1)

                    return True, [ (lhs, r) ]
                elif lhs.model.lower_bound >= rhs.model.lower_bound:
                    r = _all_operations.SI(bits=rhs.size(),
                                    stride=lhs.model.stride,
                                    lower_bound=rhs.model.lower_bound + 1,
                                    upper_bound=lhs.model.upper_bound)

                    return True, [ (lhs, r) ]
                else:
                    # We cannot handle it precisely
                    return True, [ ]
        else:
            # TODO: handle this
            #import ipdb; ipdb.set_trace()

            return True, [ ]

    def cts_simplify(self, op, args, expr, condition):
        new_expr, new_cond = getattr(self, "cts_simplifier_%s" % op)(args, expr, condition)

        return new_expr, new_cond

    def cts_handle(self, op, args):

        if len(args) == 2:
            lhs, rhs = args

            # Simplify left side
            lhs, new_cond = self.cts_simplify(lhs.op, lhs.args, lhs, (op, rhs))

            # Update args
            op, rhs = new_cond
            args = (lhs, rhs)

            sat, lst = getattr(self, "cts_handler_%s" % op)(args)

        else:
            sat, lst = getattr(self, "cts_handler_%s" % op)(args)

        return sat, lst

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

        try:
            sat, lst = self.cts_handle(expr.op, expr.args)

            return sat, lst

        except ClaripyVSASimplifierError as ex:
            l.error('VSASimplifiers raised an exception %s. Please report it.' % str(ex), exc_info=True)

            # return the dummy result
            return True, [ ]

    #
    # Backend Operations
    #

    def _identical(self, a, b, result=None):
        if type(a) != type(b):
            return False
        return a.identical(b)

    def _unique(self, obj, result=None): #pylint:disable=unused-argument,no-self-use
        if isinstance(obj, StridedInterval):
            return obj.unique
        elif isinstance(obj, ValueSet):
            return obj.unique
        elif isinstance(obj, IfProxy):
            return False
        else:
            raise BackendError('Not supported type of operand %s' % type(obj))

    def name(self, a, result=None):
        if isinstance(a, StridedInterval):
            return a.name

        else:
            return None

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
        return a.ULT(b)

    @staticmethod
    @normalize_arg_order
    def ULE(a, b):
        return a.ULE(b)

    @staticmethod
    @normalize_arg_order
    def UGT(a, b):
        return a.UGT(b)

    @staticmethod
    @normalize_arg_order
    def UGE(a, b):
        return a.UGE(b)

    @staticmethod
    @normalize_arg_order
    def SLT(a, b):
        return a.SLT(b)

    @staticmethod
    @normalize_arg_order
    def SLE(a, b):
        return a.SLE(b)

    @staticmethod
    @normalize_arg_order
    def SGT(a, b):
        return a.SGT(b)

    @staticmethod
    @normalize_arg_order
    def SGE(a, b):
        return a.SGE(b)

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
            if type(expr) not in { StridedInterval, DiscreteStridedIntervalSet, ValueSet, BVV }: #pylint:disable=unidiomatic-typecheck
                raise BackendError('Unsupported expr type %s' % type(expr))

            if type(expr) is BVV: #pylint:disable=unidiomatic-typecheck
                expr = BackendVSA.CreateStridedInterval(bits=expr.bits, to_conv=expr)

            ret = ret.concat(expr) if ret is not None else expr

        return ret

    @arg_filter
    def _size(self, arg, result=None):
        if type(arg) in { StridedInterval, DiscreteStridedIntervalSet, ValueSet, IfProxy }: #pylint:disable=unidiomatic-typecheck
            return len(arg)
        else:
            return arg.size()

    @staticmethod
    @expand_ifproxy
    def Extract(*args):
        low_bit = args[1]
        high_bit = args[0]
        expr = args[2]

        if type(expr) not in { StridedInterval, DiscreteStridedIntervalSet, ValueSet }: #pylint:disable=unidiomatic-typecheck
            raise BackendError('Unsupported expr type %s' % type(expr))

        ret = expr.extract(high_bit, low_bit)

        return ret

    @staticmethod
    @expand_ifproxy
    @convert_bvv_args
    def SignExt(*args):
        new_bits = args[0]
        expr = args[1]

        if type(expr) not in { StridedInterval, DiscreteStridedIntervalSet }: #pylint:disable=unidiomatic-typecheck
            raise BackendError('Unsupported expr type %s' % type(expr))

        return expr.sign_extend(new_bits + expr.bits)

    @staticmethod
    @expand_ifproxy
    @convert_bvv_args
    def ZeroExt(*args):
        new_bits = args[0]
        expr = args[1]

        if type(expr) not in { StridedInterval, DiscreteStridedIntervalSet }: #pylint:disable=unidiomatic-typecheck
            raise BackendError('Unsupported expr type %s' % type(expr))

        return expr.zero_extend(new_bits + expr.bits)

    @staticmethod
    @expand_ifproxy
    def Reverse(arg):
        if type(arg) not in {StridedInterval, DiscreteStridedIntervalSet, ValueSet}: #pylint:disable=unidiomatic-typecheck
            raise BackendError('Unsupported expr type %s' % type(arg))

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

        ret = args[0].widen(args[1])
        if ret is NotImplemented:
            ret = args[1].widen(args[0])

        return ret

    @staticmethod
    def CreateTopStridedInterval(bits, name=None, uninitialized=False): #pylint:disable=unused-argument,no-self-use
        return StridedInterval.top(bits, name, uninitialized=uninitialized)

from ..bv import BVV
from ..ast.base import Base
from ..operations import backend_operations_vsa_compliant, expression_set_operations
from ..vsa import StridedInterval, CreateStridedInterval, DiscreteStridedIntervalSet, ValueSet, AbstractLocation, BoolResult, TrueResult, FalseResult
from ..vsa import IfProxy
from ..errors import ClaripyBackendVSAError, ClaripyVSASimplifierError

from .. import _all_operations

BackendVSA.CreateStridedInterval = staticmethod(CreateStridedInterval)
