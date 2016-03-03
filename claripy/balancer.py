import logging
import operator

l = logging.getLogger('claripy.balancer')

class Balancer(object):
    """
    The Balancer is an equation redistributor. The idea is to take an AST and rebalance it to, for example, isolate
    unknown terms on one side of an inequality.
    """

    def __init__(self, helper, c):
        self._helper = helper
        self._truisms = [ c.ite_excavated ]
        self._processed_truisms = set()
        self.bounds = [ ]

        self.sat = True
        try:
            self._doit()
        except ClaripyBalancerUnsatError:
            self.bounds = [ ]
            self.sat = False
        except BackendError:
            l.debug("Backend error in balancer.", exc_info=True)

    @property
    def compat_ret(self):
        return (self.sat, self.replacements)

    def _replacements_iter(self):
        for o,b in self.bounds:
            yield (o, o.intersection(b))

    @property
    def replacements(self):
        return list(self._replacements_iter())

    #
    # AST helper functions
    #

    def _same_bound_bv(self, a):
        si = backends.vsa.convert(a)
        mx = self._helper.max(a)
        mn = self._helper.min(a)

        return BVS('balanced', len(a), min=mn, max=mx, stride=si._stride)

    @staticmethod
    def _reverse_comparison(a):
        try:
            new_op = opposites[a.op]
        except KeyError:
            raise ClaripyBalancerError("unable to reverse comparison %s (missing from 'opposites')", a.op)

        try:
            if new_op.startswith('__'):
                op = getattr(operator, new_op)
            else:
                op = getattr(_all_operations, new_op)
        except AttributeError:
            raise ClaripyBalancerError("unable to reverse comparison %s (AttributeError)", a.op)

        try:
            return op(*a.args[::-1])
        except ClaripyOperationError:
            # TODO: copy trace
            raise ClaripyBalancerError("unable to reverse comparison %s (ClaripyOperationError)", a.op)

    def _align_ast(self, a):
        """
        Aligns the AST so that the argument with the highest cardinality is on the left.

        :return: a new AST.
        """

        try:
            if isinstance(a, BV):
                return self._align_bv(a)
            elif isinstance(a, Bool) and len(a.args) == 2 and a.args[1].cardinality > a.args[0].cardinality:
                return self._reverse_comparison(a)
            else:
                return a
        except ClaripyBalancerError:
            return a

    #
    # Inversion
    #

    @staticmethod
    def _cardinality(a):
        return a.cardinality if isinstance(a, Base) else 0

    @staticmethod
    def _min(a, signed=False):
        if not signed: bounds = backends.vsa.convert(a)._unsigned_bounds()
        else: bounds = backends.vsa.convert(a)._signed_bounds()
        return min(mn for mn,mx in bounds)

    @staticmethod
    def _max(a, signed=False):
        if not signed: bounds = backends.vsa.convert(a)._unsigned_bounds()
        else: bounds = backends.vsa.convert(a)._signed_bounds()
        return max(mx for mn,mx in bounds)

    @staticmethod
    def _invert_comparison(a):
        return _all_operations.Not(a)

    def _align_bv(self, a):
        if a.op in commutative_operations:
            return a.make_like(a.op, tuple(sorted(a.args, key=lambda v: -self._cardinality(v))))
        else:
            try:
                op = getattr(self, '_align_'+a.op)
            except AttributeError:
                return a
            return op(a)

    def _align___sub__(self, a):
        cardinalities = [ self._cardinality(v) for v in a.args ]
        if max(cardinalities) == cardinalities[0]:
            return a

        adjusted = tuple(operator.__neg__(v) for v in a.args[1:]) + a.args[:1]
        return a.make_like('__add__', tuple(sorted(adjusted, key=lambda v: -self._cardinality(v))))

    #
    # Find bounds
    #

    def _doit(self):
        """
        This function processes the list of truisms and finds bounds for ASTs.
        """

        while len(self._truisms):
            truism = self._truisms.pop()

            if truism in self._processed_truisms:
                continue

            unpacked_truisms = self._unpack_truisms(truism)
            if len(unpacked_truisms):
                self._processed_truisms.add(truism)
                self._truisms.extend(unpacked_truisms)
                continue

            balanced_truism = self._balance(truism)
            self._handle(balanced_truism)

    #
    # Truism extractor
    #

    def _unpack_truisms(self, c):
        """
        Given a constraint, return a set of constraints that must be True for this constraint to be True.
        """

        try:
            op = getattr(self, '_unpack_truisms_'+c.op)
        except AttributeError:
            return set()
        return op(c)

    def _unpack_truisms_And(self, c):
        return set.union(*[self._unpack_truisms(a) for a in c.args])

    def _unpack_truisms_Or(self, c):
        vals = [ is_false(v) for v in c.args ]
        if all(vals):
            raise ClaripyBalancerUnsatError()
        elif vals.count(False) == 1:
            return { self._unpack_truisms(vals[vals.index(False)]) }
        else:
            return set()

    #
    # Dealing with constraints
    #

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

    #
    # Simplification routines
    #

    def _balance(self, truism):
        #print "BALANCING", truism

        # can't balance single-arg bools (Not) for now
        if len(truism.args) == 1:
            return truism

        if not isinstance(truism.args[0], Base):
            return truism

        try:
            outer_aligned = self._align_ast(truism)
            inner_aligned = outer_aligned.make_like(outer_aligned.op, (self._align_ast(outer_aligned.args[0]),) + outer_aligned.args[1:])
            if inner_aligned.args[1].cardinality > 1:
                l.debug("can't do anything because we have multiple multivalued guys")
                return truism

            if not backends.vsa.identical(inner_aligned, truism):
                import ipdb; ipdb.set_trace()

            try:
                balancer = getattr(self, "_balance_%s" % inner_aligned.args[0].op)
            except AttributeError:
                l.debug("Balance handler %s is not found in balancer. Consider implementing.", truism.args[0].op)
                return truism

            balanced = balancer(inner_aligned)
            if balanced is inner_aligned:
                #print "... balanced:", balanced
                return balanced
            else:
                return self._balance(balanced)
        except ClaripyBalancerError:
            l.warning("Balance handler for operation %s raised exception.", truism.args[0].op)
            return truism

    @staticmethod
    def _balance_Reverse(truism):
        if truism.op == '__eq__' or truism.op == '__ne__':
            return truism.make_like(truism.op, truism.args[0].args[0], truism.args[1].reversed)
        else:
            return truism

    @staticmethod
    def _balance___add__(truism):
        new_lhs = truism.args[0].args[0]
        old_rhs = truism.args[1]
        other_adds = truism.args[0].args[1:]
        new_rhs = truism.args[0].make_like('__sub__', (old_rhs,) + other_adds)
        return truism.make_like(truism.op, (new_lhs, new_rhs))

    @staticmethod
    def _balance_ZeroExt(truism):
        num_zeroes, inner = truism.args[0].args
        other_side = truism.args[1][len(truism.args[1])-1:len(truism.args[1])-num_zeroes]

        if is_true(other_side == 0):
            # We can safely eliminate this layer of ZeroExt
            new_args = (inner, truism.args[1][len(truism.args[1])-num_zeroes-1:0])
            return truism.make_like(truism.op, new_args)

        return truism

    @staticmethod
    def _balance_SignExt(truism):
        num_zeroes = truism.args[0].args[0]
        left_side = truism.args[0][len(truism.args[1])-1:len(truism.args[1])-num_zeroes]
        other_side = truism.args[1][len(truism.args[1])-1:len(truism.args[1])-num_zeroes]

        #TODO: what if this is a set value, but *not* the same as other_side
        if backends.vsa.identical(left_side, other_side):
            # We can safely eliminate this layer of ZeroExt
            new_args = (truism.args[0].args[1], truism.args[1][len(truism.args[1])-num_zeroes-1:0])
            return truism.make_like(truism.op, new_args)

        return truism

    @staticmethod
    def _balance_Extract(truism):
        size = len(truism.args[0])
        high, low, inner = truism.args[0].args

        if high < size-1:
            left_msb = inner[size-1:high+1]
            left_msb_zero = is_true(left_msb == 0)
        else:
            left_msb = None
            left_msb_zero = None

        if low > 0:
            left_lsb = inner[high-1:0]
            left_lsb_zero = is_true(left_lsb == 0)
        else:
            left_lsb = None
            left_lsb_zero = None

        if left_msb_zero and left_lsb_zero:
            new_left = inner
            new_right = _all_operations.Concat(BVV(0, len(left_msb)), truism.arg[1], BVV(0, len(left_lsb)))
            return truism.make_like(truism.op, (new_left, new_right))
        elif left_msb_zero:
            new_left = inner[high:0]
            new_right = _all_operations.Concat(BVV(0, len(left_msb)), truism.arg[1])
            return truism.make_like(truism.op, (new_left, new_right))
        elif left_lsb_zero:
            new_left = inner[size-1:low]
            new_right = _all_operations.Concat(truism.arg[1], BVV(0, len(left_lsb)))
            return truism.make_like(truism.op, (new_left, new_right))
        else:
            #TODO: handle non-zero single-valued cases
            return truism

    @staticmethod
    def _balance_Concat(truism):
        size = len(truism.args[0])
        left_msb = truism.args[0].args[0]
        right_msb = truism.args[1][size-1:size-len(left_msb)]

        if is_true(left_msb == 0) and is_true(right_msb == 0):
            # we can cut these guys off!
            remaining_left = _all_operations.Concat(truism.args[0].args[1:])
            remaining_right = truism.args[1][size-len(left_msb)-1:0]
            return truism.make_like(truism.op, (remaining_left, remaining_right))
        else:
            #TODO: handle non-zero single-valued cases
            return truism

    def _balance_If(self, truism):
        condition, true_expr, false_expr = truism.args[0]

        try:
            if truism.op.startswith('__'):
                true_condition = getattr(operator, truism.op)(true_expr, truism.args[1])
                false_condition = getattr(operator, truism.op)(false_expr, truism.args[1])
            else:
                true_condition = getattr(_all_operations, truism.op)(true_expr, truism.args[1])
                false_condition = getattr(_all_operations, truism.op)(false_expr, truism.args[1])
        except ClaripyOperationError:
            # the condition was probably a Not (TODO)
            return truism

        can_true = backends.vsa.has_true(true_condition)
        can_false = backends.vsa.has_true(false_condition)
        must_true = backends.vsa.is_true(true_condition)
        must_false = backends.vsa.is_true(false_condition)

        if can_true and can_false:
            # always satisfiable
            return truism
        elif not (can_true or can_false):
            # neither are satisfiable. This truism is fucked
            raise ClaripyBalancerUnsatError()
        elif must_true or (can_true and not can_false):
            # it will always be true
            self._truisms.append(condition)
            return truism.make_like(truism.op, (true_expr, truism.args[1]))
        elif must_false or (can_false and not can_true):
            # it will always be false
            self._truisms.append(self._invert_comparison(condition))
            return truism.make_like(truism.op, (false_expr, truism.args[1]))

    #
    # Constraint handlers
    #

    def _handle(self, truism):
        #print "HANDLING", truism

        if is_false(truism):
            raise ClaripyBalancerUnsatError()
        elif is_true(truism):
            return
        elif self._cardinality(truism.args[0]) == 1:
            # we are down to single-cardinality arguments, so our work is not
            # necessary
            return

        try:
            handler = getattr(self, "_handle_%s" % truism.op)
        except AttributeError:
            l.debug("No handler for operation %s", truism.op)
            return

        bounds = handler(truism)
        self.bounds.extend(bounds)

    def _handle_comparison(self, truism):
        """
        Handles all comparisons.
        """

        #print "COMP:", truism

        is_lt, is_equal, is_unsigned = self.comparison_info[truism.op]

        size = len(truism.args[0])
        int_max = 2**size-1 if is_unsigned else 2**(size-1)-1
        int_min = 0 if is_unsigned else -2**(size-1)

        left_min = self._min(truism.args[0], signed=not is_unsigned)
        left_max = self._max(truism.args[0], signed=not is_unsigned)
        right_min = self._min(truism.args[1], signed=not is_unsigned)
        right_max = self._max(truism.args[1], signed=not is_unsigned)

        bound_max = right_max if is_equal else (right_max-1)
        bound_min = right_min if is_equal else (right_min-1)

        if is_lt and bound_max < int_min:
            # if the bound max is negative and we're unsigned less than, we're fucked
            raise ClaripyBalancerUnsatError()
        elif not is_lt and bound_min > int_max:
            # if the bound min is too big, we're fucked
            raise ClaripyBalancerUnsatError()

        current_min = int_min
        current_max = int_max

        if is_lt:
            current_max = min(int_max, left_max, bound_max)
        else:
            current_min = max(int_min, left_min, bound_min)

        return [ (truism.args[0], BVS('bound_inequality', size, min=current_min, max=current_max, stride=1)) ]

    def _handle_eq_ne(self, truism):
        lhs, rhs = truism.args

        eq_comparison = truism.op == '__eq__'

        if eq_comparison:
            if rhs.cardinality != 1:
                common = self._same_bound_bv(lhs.intersection(rhs))
                return [ (lhs, common), (rhs, common) ]
            else:
                return [ (lhs, rhs) ]
        else:
            if rhs.cardinality == 1:
                val = self._helper.eval(rhs, 1)[0]
                max_int = vsa.StridedInterval.max_int(len(rhs))

                if val == 0:
                    other_si = BVS('bound_ne_min', len(rhs), min=val+1)
                    return [ (lhs, other_si) ]
                elif val == max_int or val == -1:
                    other_si = BVS('bound_ne_max', len(rhs), max=max_int-1)
                    return [ (lhs, self._same_bound_bv(other_si.intersection(lhs))) ]
                else:
                    return [ ]
            return [ ]

    def _handle_If(self, truism):
        if is_false(truism.args[2]):
            self._truisms.append(truism.args[0])
        elif is_false(truism.args[1]):
            self._truisms.append(self._invert_comparison(truism.args[0]))

        return [ ]

    _handle___lt__ = _handle_comparison
    _handle___le__ = _handle_comparison
    _handle___gt__ = _handle_comparison
    _handle___ge__ = _handle_comparison
    _handle_ULT = _handle_comparison
    _handle_ULE = _handle_comparison
    _handle_UGT = _handle_comparison
    _handle_UGE = _handle_comparison
    _handle_SLT = _handle_comparison
    _handle_SLE = _handle_comparison
    _handle_SGT = _handle_comparison
    _handle_SGE = _handle_comparison
    _handle___ne__ = _handle_eq_ne
    _handle___eq__ = _handle_eq_ne

def is_true(a): return backends.vsa.is_true(a)
def is_false(a): return backends.vsa.is_false(a)

from .errors import ClaripyBalancerError, ClaripyBalancerUnsatError, ClaripyOperationError, BackendError
from .ast.base import Base
from .ast.bool import Bool
from .ast.bv import BVV, BVS, BV
from . import _all_operations
from .backend_manager import backends
from . import vsa
from .operations import opposites, commutative_operations
