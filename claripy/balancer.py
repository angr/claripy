import logging
import operator

l = logging.getLogger('claripy.balancer')

class Balancer:
    """
    The Balancer is an equation redistributor. The idea is to take an AST and rebalance it to, for example, isolate
    unknown terms on one side of an inequality.
    """

    def __init__(self, helper, c, validation_frontend=None):
        self._helper = helper
        self._validation_frontend = validation_frontend
        self._truisms = [ ]
        self._processed_truisms = set()
        self._identified_assumptions = set()
        self._lower_bounds = { }
        self._upper_bounds = { }

        self._queue_truism(c.ite_excavated)

        self.sat = True
        try:
            self._doit()
        except ClaripyBalancerUnsatError:
            self.bounds = { }
            self.sat = False
        except BackendError:
            l.debug("Backend error in balancer.", exc_info=True)

    @property
    def compat_ret(self):
        return (self.sat, self.replacements)

    def _replacements_iter(self):
        all_keys = set(self._lower_bounds.keys()) | set(self._upper_bounds.keys())
        for k in all_keys:
            max_int = (1 << len(k.ast)) - 1
            min_int = 0
            mn = self._lower_bounds.get(k, min_int)
            mx = self._upper_bounds.get(k, max_int)
            bound_si = BVS('bound', len(k.ast), min=mn, max=mx)
            l.debug("Yielding bound %s for %s.", bound_si, k.ast)
            if k.ast.op == 'Reverse':
                yield (k.ast.args[0], k.ast.intersection(bound_si).reversed)
            else:
                yield (k.ast, k.ast.intersection(bound_si))

    def _add_lower_bound(self, o, b):
        l.debug("Adding lower bound %s for %s.", b, o)
        if o.cache_key in self._lower_bounds:
            old_b = self._lower_bounds[o.cache_key]
            l.debug("... old bound: %s", old_b)
            b = max(b, old_b)
            l.debug("... new bound: %s", b)

        if self._validation_frontend is not None:
            emin = self._validation_frontend.min(o)
            bmin = self._helper.min(b)
            assert emin >= bmin

        self._lower_bounds[o.cache_key] = b

    def _add_upper_bound(self, o, b):
        l.debug("Adding upper bound %s for %s.", b, o)
        if o.cache_key in self._upper_bounds:
            old_b = self._upper_bounds[o.cache_key]
            l.debug("... old bound: %s", old_b)
            b = min(b, old_b)
            l.debug("... new bound: %s", b)

        if self._validation_frontend is not None:
            emax = self._validation_frontend.max(o)
            bmax = self._helper.max(b)
            assert emax <= bmax

        self._upper_bounds[o.cache_key] = b

    @property
    def replacements(self):
        return list(self._replacements_iter())

    #
    # AST helper functions
    #

    def _same_bound_bv(self, a):
        si = backends.vsa.convert(a)
        mx = self._max(a)
        mn = self._min(a)
        return BVS('bounds', len(a), min=mn, max=mx, stride=si._stride)

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

    def _range(self, a, signed=False):
        return (self._min(a, signed=signed), self._max(a, signed=signed))

    @staticmethod
    def _invert_comparison(a):
        return _all_operations.Not(a)

    #
    # Truism alignment
    #

    def _align_truism(self, truism):
        outer_aligned = self._align_ast(truism)
        inner_aligned = outer_aligned.make_like(outer_aligned.op, (self._align_ast(outer_aligned.args[0]),) + outer_aligned.args[1:])

        if not backends.vsa.identical(inner_aligned, truism):
            l.critical("ERROR: the balancer is messing up an AST. This must be looked into. Please submit the binary and script to the angr project, if possible. Outer op is %s and inner op is %s.", truism.op, truism.args[0].op)
            return truism

        return inner_aligned

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

    @staticmethod
    def _reverse_comparison(a):
        try:
            new_op = opposites[a.op]
        except KeyError:
            raise ClaripyBalancerError("unable to reverse comparison %s (missing from 'opposites')" % a.op)

        try:
            if new_op.startswith('__'):
                op = getattr(operator, new_op)
            else:
                op = getattr(_all_operations, new_op)
        except AttributeError:
            raise ClaripyBalancerError("unable to reverse comparison %s (AttributeError)" % a.op)

        try:
            return op(*a.args[::-1])
        except ClaripyOperationError:
            # TODO: copy trace
            raise ClaripyBalancerError("unable to reverse comparison %s (ClaripyOperationError)" % a.op)

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
            self._processed_truisms.add(truism)
            if len(unpacked_truisms):
                self._queue_truisms(unpacked_truisms, check_true=True)
                continue

            if not self._handleable_truism(truism):
                continue

            truism = self._adjust_truism(truism)

            assumptions = self._get_assumptions(truism)
            if truism not in self._identified_assumptions and len(assumptions):
                l.debug("Queued assumptions %s for truism %s.", assumptions, truism)
                self._truisms.extend(assumptions)
                self._identified_assumptions.update(assumptions)

            l.debug("Processing truism %s", truism)
            balanced_truism = self._balance(truism)
            l.debug("... handling")
            self._handle(balanced_truism)

    def _queue_truism(self, t, check_true=False):
        if not check_true:
            self._truisms.append(t)
        elif check_true and not is_true(t):
            self._truisms.append(t)

    def _queue_truisms(self, ts, check_true=False):
        if check_true:
            self._truisms.extend(t for t in ts if not is_true(t))
        else:
            self._truisms.extend(ts)

    @staticmethod
    def _handleable_truism(t):
        """
        Checks whether we can handle this truism. The truism should already be aligned.
        """
        if len(t.args) < 2:
            l.debug("can't do anything with an unop bool")
        elif t.args[0].cardinality > 1 and t.args[1].cardinality > 1:
            l.debug("can't do anything because we have multiple multivalued guys")
            return False
        else:
            return True

    @staticmethod
    def _adjust_truism(t):
        """
        Swap the operands of the truism if the unknown variable is on the right side and the concrete value is on the
        left side.
        """
        if t.args[0].cardinality == 1 and t.args[1].cardinality > 1:
            swapped = Balancer._reverse_comparison(t)
            return swapped
        return t


    #
    # Assumptions management
    #

    @staticmethod
    def _get_assumptions(t):
        """
        Given a constraint, _get_assumptions() returns a set of constraints that are implicitly
        assumed to be true. For example, `x <= 10` would return `x >= 0`.
        """

        if t.op in ('__le__', '__lt__', 'ULE', 'ULT'):
            return [ t.args[0] >= 0 ]
        elif t.op in ('__ge__', '__gt__', 'UGE', 'UGT'):
            return [ t.args[0] <= 2**len(t.args[0])-1 ]
        elif t.op in ('SLE', 'SLT'):
            return [ _all_operations.SGE(t.args[0], -(1 << (len(t.args[0])-1))) ]
        elif t.op in ('SGE', 'SGT'):
            return [ _all_operations.SLE(t.args[0], (1 << (len(t.args[0])-1)) - 1) ]
        else:
            return [ ]

    #
    # Truism extractor
    #

    def _unpack_truisms(self, c):
        """
        Given a constraint, _unpack_truisms() returns a set of constraints that must be True
        this constraint to be True.
        """

        try:
            op = getattr(self, '_unpack_truisms_'+c.op)
        except AttributeError:
            return set()
        return op(c)

    def _unpack_truisms_And(self, c):
        return set.union(*[self._unpack_truisms(a) for a in c.args])

    def _unpack_truisms_Not(self, c):
        if c.args[0].op == 'And':
            return self._unpack_truisms(_all_operations.Or(*[_all_operations.Not(a) for a in c.args[0].args]))
        elif c.args[0].op == 'Or':
            return self._unpack_truisms(_all_operations.And(*[_all_operations.Not(a) for a in c.args[0].args]))
        else:
            return set()

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
        l.debug("Balancing %s", truism)

        # can't balance single-arg bools (Not) for now
        if len(truism.args) == 1:
            return truism

        if not isinstance(truism.args[0], Base):
            return truism

        try:
            inner_aligned = self._align_truism(truism)
            if inner_aligned.args[1].cardinality > 1:
                l.debug("can't do anything because we have multiple multivalued guys")
                return truism

            try:
                balancer = getattr(self, "_balance_%s" % inner_aligned.args[0].op)
            except AttributeError:
                l.debug("Balance handler %s is not found in balancer. Consider implementing.", truism.args[0].op)
                return truism

            balanced = balancer(inner_aligned)
            if balanced is inner_aligned:
                # print("... balanced:", balanced)
                return balanced
            else:
                return self._balance(balanced)
        except ClaripyBalancerError:
            l.warning("Balance handler for operation %s raised exception.", truism.args[0].op)
            return truism

    @staticmethod
    def _balance_Reverse(truism):
        if truism.op in ['__eq__', '__ne__']:
            return truism.make_like(truism.op, (truism.args[0].args[0], truism.args[1].reversed))
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
    def _balance___sub__(truism):
        new_lhs = truism.args[0].args[0]
        old_rhs = truism.args[1]
        other_adds = truism.args[0].args[1:]
        new_rhs = truism.args[0].make_like('__add__', (old_rhs,) + other_adds)
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
        high, low, inner = truism.args[0].args
        inner_size = len(inner)

        if high < inner_size-1:
            left_msb = inner[inner_size-1:high+1]
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
            new_right = _all_operations.Concat(BVV(0, len(left_msb)), truism.args[1], BVV(0, len(left_lsb)))
            return truism.make_like(truism.op, (new_left, new_right))
        elif left_msb_zero:
            new_left = inner
            new_right = _all_operations.Concat(BVV(0, len(left_msb)), truism.args[1])
            return truism.make_like(truism.op, (new_left, new_right))
        elif left_lsb_zero:
            new_left = inner
            new_right = _all_operations.Concat(truism.args[1], BVV(0, len(left_lsb)))
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
            remaining_left = _all_operations.Concat(*truism.args[0].args[1:])
            remaining_right = truism.args[1][size-len(left_msb)-1:0]
            return truism.make_like(truism.op, (remaining_left, remaining_right))
        else:
            #TODO: handle non-zero single-valued cases
            return truism

    def _balance___lshift__(self, truism):
        lhs = truism.args[0]
        rhs = truism.args[1]
        shift_amount_expr = lhs.args[1]
        expr = lhs.args[0]

        shift_amount_values = self._helper.eval(shift_amount_expr, 2)
        if len(shift_amount_values) != 1:
            return truism
        shift_amount = shift_amount_values[0]

        rhs_lower = _all_operations.Extract(shift_amount - 1, 0, rhs)
        rhs_lower_values = self._helper.eval(rhs_lower, 2)
        if len(rhs_lower_values) == 1 and rhs_lower_values[0] == 0:
            # we can remove the __lshift__

            return truism.make_like(truism.op, (expr, rhs >> shift_amount))

        return truism

    def _balance_If(self, truism):
        condition, true_expr, false_expr = truism.args[0].args

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
            self._queue_truism(condition)
            return truism.make_like(truism.op, (true_expr, truism.args[1]))
        elif must_false or (can_false and not can_true):
            # it will always be false
            self._queue_truism(self._invert_comparison(condition))
            return truism.make_like(truism.op, (false_expr, truism.args[1]))

    #
    # Constraint handlers
    #

    def _handle(self, truism):
        l.debug("Handling %s", truism)

        if is_false(truism):
            raise ClaripyBalancerUnsatError()
        elif self._cardinality(truism.args[0]) == 1:
            # we are down to single-cardinality arguments, so our work is not
            # necessary
            return

        try:
            handler = getattr(self, "_handle_%s" % truism.op)
        except AttributeError:
            l.debug("No handler for operation %s", truism.op)
            return
        handler(truism)

    def _handle_comparison(self, truism):
        """
        Handles all comparisons.
        """

        # print("COMP:", truism)

        is_lt, is_equal, is_unsigned = self.comparison_info[truism.op]

        size = len(truism.args[0])
        int_max = 2**size-1 if is_unsigned else 2**(size-1)-1
        int_min = -2**(size-1)

        left_min = self._min(truism.args[0], signed=not is_unsigned)
        left_max = self._max(truism.args[0], signed=not is_unsigned)
        right_min = self._min(truism.args[1], signed=not is_unsigned)
        right_max = self._max(truism.args[1], signed=not is_unsigned)

        bound_max = right_max if is_equal else (right_max-1 if is_lt else right_max+1)
        bound_min = right_min if is_equal else (right_min-1 if is_lt else right_min+1)

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
            self._add_upper_bound(truism.args[0], current_max)
        else:
            current_min = max(int_min, left_min, bound_min)
            self._add_lower_bound(truism.args[0], current_min)

    def _handle___eq__(self, truism):
        lhs, rhs = truism.args
        if rhs.cardinality != 1:
            common = self._same_bound_bv(lhs.intersection(rhs))
            mn, mx = self._range(common)
            self._add_upper_bound(lhs, mx)
            self._add_upper_bound(rhs, mx)
            self._add_lower_bound(lhs, mn)
            self._add_lower_bound(rhs, mn)
        else:
            mn, mx = self._range(rhs)
            self._add_upper_bound(lhs, mx)
            self._add_lower_bound(lhs, mn)

    def _handle___ne__(self, truism):
        lhs, rhs = truism.args
        if rhs.cardinality == 1:
            val = self._helper.eval(rhs, 1)[0]
            max_int = vsa.StridedInterval.max_int(len(rhs))

            if val == 0:
                self._add_lower_bound(lhs, val+1)
            elif val == max_int or val == -1:
                self._add_upper_bound(lhs, max_int-1)

    def _handle_If(self, truism):
        if is_false(truism.args[2]):
            self._queue_truism(truism.args[0])
        elif is_false(truism.args[1]):
            self._queue_truism(self._invert_comparison(truism.args[0]))

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
