import logging

l = logging.getLogger('claripy.balancer')

class Balancer(object):
    '''
    The Balancer is an equation redistributor. The idea is to take an AST and
    rebalance it to, for example, isolate unknown terms on one side of an
    inequality.
    '''

    def __init__(self, backend):
        self._backend = backend

    def constraint_to_si(self, expr):
        """
        We take in constraints, and return bounds (in the form of strided intervals) for the variables involved.

        :param expr: The constraint
        :return: whether the expr is satisfiable (boolean), and a list of tuples in form of
                (original_si, constrained_si).
        """

        try:
            sat, lst = self._handle(expr.op, expr.args)
            return sat, lst

        except (BackendError,ClaripyBalancerError) as ex:
            l.error('VSASimplifiers raised an exception %s. Please report it.', str(ex), exc_info=True)

            # return the dummy result
            return True, [ ]

    def _simplify(self, op, args, expr, condition):
        handler_name = "_simplify_%s" % op
        if not hasattr(self, handler_name):
            l.warning('Simplification handler "%s" is not found in balancer. Consider implementing.', handler_name)
            return expr, condition

        new_expr, new_cond = getattr(self, "_simplify_%s" % op)(args, expr, condition)
        return new_expr, new_cond

    def _handle(self, op, args):
        if len(args) == 2:
            lhs, rhs = args

            # Simplify left side
            lhs, new_cond = self._simplify(lhs.op, lhs.args, lhs, (op, rhs))

            # Update args
            op, rhs = new_cond
            args = (lhs, rhs)

            sat, lst = getattr(self, "_handle_%s" % op)(args)

        else:
            sat, lst = getattr(self, "_handle_%s" % op)(args)

        return sat, lst

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

    def _simplify_ZeroExt(self, args, expr, condition):
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
                is_true(cond_arg[ expr.size() - 1 : expr.size() - extended_bits ] == 0):
            # We can safely eliminate this layer of ZeroExt
            if cond_arg.size() < arg.size():
                larger_cond_arg = cond_arg.zero_extend(arg.size() - cond_arg.size())
                larger_cond_arg_bo = self._backend.convert(larger_cond_arg)
                if not isinstance(larger_cond_arg_bo, Base):
                    return self._simplify(arg.op, arg.args, arg, (cond_op, larger_cond_arg))
            else:
                return self._simplify(arg.op, arg.args, arg, (cond_op, cond_arg[ arg.size() - 1 : 0 ]))

        else:
            # TODO: We may also handle the '__eq__' and '__ne__' case
            # We cannot handle this...
            return expr, condition

    def _simplify_BVS(self, args, expr, condition): #pylint:disable=no-self-use,unused-argument
        return expr, condition

    def _simplify_SignExt(self, args, expr, condition):
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
                is_true(cond_arg[expr.size() - 1: expr.size() - extended_bits] == 0):
            # We can safely eliminate this layer of SignExt
            if cond_arg.size() < arg.size():
                larger_cond_arg = cond_arg.zero_extend(arg.size() - cond_arg.size()).resolved()
                if not isinstance(larger_cond_arg, Base):
                    return self._simplify(arg.op, arg.args, arg, (cond_op, larger_cond_arg))
            else:
                return self._simplify(arg.op, arg.args, arg, (cond_op, cond_arg[arg.size() - 1: 0]))

        else:
            # TODO: We may also handle the '__eq__' and '__ne__' case
            # We cannot handle this...
            return expr, condition

    def _simplify_Extract(self, args, expr, condition):
        '''
        Convert Extract(a, b, If(...)) to If(..., Extract(a, b, ...), Extract(a, b, ...))

        :param args:
        :return:
        '''

        high, low, to_extract = args
        cond_operation, cond_operand = condition
        # Make sure the condition operand has the same size as to_extract
        new_condition = cond_operation, _all_operations.ZeroExt((high - low + 1), cond_operand)
        ast, cond = self._simplify(to_extract.op, to_extract.args, to_extract, new_condition)

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
            cond_arg_bo = self._backend.convert(cond_arg)
            if type(cond_arg_bo) in (int, long): #pylint:disable=unidiomatic-typecheck
                cond_arg = _all_operations.BVV(cond_arg, ast.size())
            elif isinstance(cond_arg_bo, vsa.StridedInterval):
                if ast.size() > cond_arg.size():
                    # Make sure two operands have the same size
                    cond_arg = _all_operations.ZeroExt(ast.size() - cond_arg.size(), cond_arg)

            if cond_arg.size() - 1 < high + 1 or \
                    is_true(cond_arg[cond_arg.size() - 1 : high + 1] == 0):
                # The upper part doesn't matter
                # We can handle it
                return self._simplify(ast.op, ast.args, ast, (cond_op, cond_arg))
            else:
                # We cannot further simplify it
                return expr, condition

        return new_ifproxy, condition

    def _simplify_Concat(self, args, expr, condition):
        '''
        Convert Concat(a, If(...)) to If(..., Concat(a, ...), Concat(a, ...))

        :param args:
        :return:
        '''

        new_args = [ self._simplify(ex.op, ex.args, ex, condition) for ex in args ]

        ifproxy_conds = set([ a.args[0] for a, new_cond in new_args if a.op == 'If' ])

        if len(ifproxy_conds) == 0:
            # Let's check if we can remove this layer of Concat
            cond = condition[1]
            if len(args) == 2:
                if cond.size() - 1 >= cond.size() - args[0].size():
                    if is_true(args[0] == cond[ cond.size() - 1 : cond.size() - args[0].size() ]):
                        # Yes! We can remove it!
                        # TODO: This is hackish...
                        new_cond = (condition[0], cond[ cond.size() - args[0].size() - 1 : 0])
                        return self._simplify(args[1].op, args[1].args, args[1], new_cond)

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

    def _simplify_Reverse(self, args, expr, condition): #pylint:disable=unused-argument
        # TODO: How should we deal with Reverse in a smart way?
        arg = args[0]
        return self._simplify(arg.op, arg.args, arg, condition)

    def _simplify___and__(self, args, expr, condition):
        argl, argr = args
        if argl.structurally_match(argr):
            # Operands are the same
            # Safely remove the __and__ operation
            return self._simplify(argl.op, argl.args, argl, condition)
        else:
            # We cannot handle it
            return expr, condition

    def _simplify___add__(self, args, expr, condition):
        argl, argr = args

        if argl.singlevalued:
            new_cond = (condition[0], condition[1] - argl)
            return self._simplify(argr.op, argr.args, argr, new_cond)
        elif argr.singlevalued:
            new_cond = (condition[0], condition[1] - argr)
            return self._simplify(argl.op, argl.args, argl, new_cond)
        else:
            return expr, condition

    def _simplify___radd__(self, args, expr, condition):
        return self._simplify___add__((args[1], args[0]), expr, condition)

    # TODO: simplify __sub__

    def _handle_comparison(self, args, comp=None):
        """
        Handles all comparisons.
        :param args:
        :param comp:
        :return:
        """

        if comp in self.comparison_info:
            is_lt, is_equal, is_unsigned = self.comparison_info[comp]
        else:
            raise ClaripyBalancerError('Support for comparison %s is not implemented. Please report it.' % comp)

        lhs, rhs = args

        if not isinstance(lhs, Base):
            raise ClaripyBalancerError('Left-hand-side expression is not an AST object.')

        lhs_bo = self._backend.convert(lhs)
        rhs_bo = self._backend.convert(rhs)

        # Maybe the target variable is the rhs
        if lhs.cardinality == 1 or lhs_bo.is_empty:
            new_op = self.reversed_operations[comp]
            new_lhs, new_rhs = rhs, lhs
            return self._handle(new_op, (new_lhs, new_rhs))

        if lhs.op == 'If':
            condition, trueexpr, falseexpr = lhs.args
            trueexpr_bo = self._backend.convert(trueexpr)
            falseexpr_bo = self._backend.convert(falseexpr)

            if is_unsigned:
                if is_lt:
                    if is_equal:
                        take_true = is_true(trueexpr_bo.ULE(rhs_bo))
                        take_false = is_true(falseexpr_bo.ULE(rhs_bo))
                    else:
                        take_true = is_true(falseexpr_bo.ULT(rhs_bo))
                        take_false = is_true(trueexpr_bo.ULT(rhs_bo))
                else:
                    if is_equal:
                        take_true = is_true(trueexpr_bo.UGE(rhs_bo))
                        take_false = is_true(falseexpr_bo.UGE(rhs_bo))
                    else:
                        take_true = is_true(trueexpr_bo.UGT(rhs_bo))
                        take_false = is_true(falseexpr_bo.UGT(rhs_bo))
            else:
                if is_lt:
                    if is_equal:
                        take_true = is_true(trueexpr_bo <= rhs_bo)
                        take_false = is_true(falseexpr_bo <= rhs_bo)
                    else:
                        take_true = is_true(trueexpr_bo < rhs_bo)
                        take_false = is_true(falseexpr_bo < rhs_bo)
                else:
                    if is_equal:
                        take_true = is_true(trueexpr_bo >= rhs_bo)
                        take_false = is_true(falseexpr_bo >= rhs_bo)
                    else:
                        take_true = is_true(trueexpr_bo > rhs_bo)
                        take_false = is_true(falseexpr_bo > rhs_bo)

            if take_true and take_false:
                # It's always satisfiable
                return True, [ ]
            elif take_true:
                return self._handle(condition.op, condition.args)
            elif take_false:
                rev_op = self.reversed_operations[condition.op]
                return self._handle(rev_op, condition.args)
            else:
                # Not satisfiable
                return False, [ ]

        elif isinstance(rhs_bo, vsa.StridedInterval) and isinstance(lhs_bo, vsa.StridedInterval):
            if isinstance(lhs_bo, Base):
                # It cannot be computed by our backend...
                # We just give up for now
                return True, [ ]

            stride = lhs_bo.stride

            if is_lt:
                # < or <=
                if is_unsigned: lb = 0
                else: lb = vsa.StridedInterval.min_int(rhs.length)

                ub = rhs_bo.upper_bound
                if not is_equal:
                    # <
                    ub = ub - 1

            else:
                # > or >=
                if is_unsigned: ub = vsa.StridedInterval.max_int(rhs.length)
                else: ub = vsa.StridedInterval.max_int(rhs.length - 1)

                lb = rhs_bo.lower_bound
                if not is_equal:
                    # >
                    lb = lb + 1

            if stride == 0 and lb != ub:
                # Make sure the final vsa.StridedInterval is always meaningful. See issue #55.
                stride = 1

            si_replacement = _all_operations.SI(bits=rhs.length, stride=stride, lower_bound=lb, upper_bound=ub)
            return True, [(lhs, si_replacement)]

        else:
            return True, [ ]

    def _handle___lt__(self, args): return self._handle_comparison(args, comp='__lt__')
    def _handle___le__(self, args): return self._handle_comparison(args, comp='__le__')
    def _handle___gt__(self, args): return self._handle_comparison(args, comp='__gt__')
    def _handle___ge__(self, args): return self._handle_comparison(args, comp='__ge__')
    def _handle_ULT(self, args): return self._handle_comparison(args, comp='ULT')
    def _handle_ULE(self, args): return self._handle_comparison(args, comp='ULE')
    def _handle_UGT(self, args): return self._handle_comparison(args, comp='UGT')
    def _handle_UGE(self, args): return self._handle_comparison(args, comp='UGE')
    def _handle_SLT(self, args): return self._handle_comparison(args, comp='SLT')
    def _handle_SLE(self, args): return self._handle_comparison(args, comp='SLE')
    def _handle_SGT(self, args): return self._handle_comparison(args, comp='SGT')
    def _handle_SGE(self, args): return self._handle_comparison(args, comp='SGE')

    def _handle_BoolV(self, args): #pylint:disable=no-self-use
        return args[0], [ ]

    def _handle_Not(self, args):
        """
        The argument should be False

        :param args:
        :return:
        """

        a = args[0]
        expr_op = a.op
        expr_args = a.args

        # Reverse the op
        try:
            expr_op = self.reversed_operations[expr_op]
            return self._handle(expr_op, expr_args)
        except KeyError:
            return True, [ ]

    def _handle_And(self, args):
        """

        :param args:
        :return:
        """

        sat = True
        lst = [ ]

        # Both sides must be true
        for arg in args:
            sat_, lst_ = self._handle(arg.op, arg.args)

            sat &= sat_
            lst.extend(lst_)

        if not sat:
            lst = [ ]

        return sat, lst

    def _handle_Or(self, args):
        if len(args) == 1:
            return self._handle(args[0].op, args[0].args)

        else:
            if len(args) > 0:
                if any(self._handle(a.op, a.args)[0] for a in args):
                    return True, [ ]
                else:
                    return False, [ ]
            return True, [ ]

    def _handle___ne__(self, args):
        return self._handle_eq_ne(args, False)

    def _handle___eq__(self, args):
        return self._handle_eq_ne(args, True)

    def _handle_eq_ne(self, args, is_eq):
        """

        :param args:
        :return: True or False, and a list of (original_si, constrained_si) tuples
        """

        lhs, rhs = args

        if not isinstance(lhs, Base):
            raise ClaripyBalancerError('Left-hand-side expression is not an AST object.')

        size = lhs.size()

        if type(rhs) in (int, long): #pylint:disable=unidiomatic-typecheck
            # Convert it into a BVV
            rhs = _all_operations.BVV(rhs, size)

        if not isinstance(rhs, Base):
            raise ClaripyBalancerError('Right-hand-side expression cannot be converted to an AST object.')

        # TODO: Make sure the rhs doesn't contain any IfProxy

        lhs_bo = self._backend.convert(lhs)

        if lhs.op == 'If':
            condition, trueexpr, falseexpr = lhs.args

            if is_eq:
                # __eq__
                take_true = is_true(rhs == trueexpr)
                take_false = is_true(rhs == falseexpr)
            else:
                # __ne__
                take_true = is_true(rhs == falseexpr)
                take_false = is_true(rhs == trueexpr)

            if take_true and take_false:
                # It's always satisfiable
                return True, [ ]

            elif take_true:
                # We take the true side
                return self._handle(condition.op, condition.args)

            elif take_false:
                # We take the false side

                # Reverse the operation first
                rev_op = self.reversed_operations[condition.op]

                return self._handle(rev_op, condition.args)

            else:
                # Not satisfiable
                return False, [ ]
        elif isinstance(lhs_bo, vsa.StridedInterval):
            rhs_bo = self._backend.convert(rhs)

            if is_eq:
                return True, [ (lhs, rhs)]
            else:
                rhs_bo = self._backend.convert(rhs)

                if lhs_bo.upper_bound <= rhs_bo.upper_bound:
                    r = _all_operations.SI(bits=rhs_bo.bits, stride=lhs_bo.stride, lower_bound=lhs_bo.lower_bound, upper_bound=rhs_bo.lower_bound - 1)
                    return True, [ (lhs, r) ]
                elif lhs_bo.lower_bound >= rhs_bo.lower_bound:
                    r = _all_operations.SI(bits=rhs_bo.bits, stride=lhs_bo.stride, lower_bound=rhs_bo.lower_bound + 1, upper_bound=lhs_bo.upper_bound)
                    return True, [ (lhs, r) ]
                else:
                    # We cannot handle it precisely
                    return True, [ ]
        else:
            # TODO: handle this
            return True, [ ]

def is_true(a): return backends.vsa.is_true(a)
def is_false(a): return backends.vsa.is_false(a)

from .errors import ClaripyBalancerError, ClaripyBackendVSAError, BackendError
from .ast.base import Base
from . import _all_operations
from .backend_manager import backends
from . import vsa
