from __future__ import annotations

import logging
import operator

import claripy

from . import vsa
from .ast.base import Base
from .ast.bool import Bool
from .ast.bv import BV, BVS, BVV
from .backend_manager import backends
from .errors import BackendError, ClaripyBalancerError, ClaripyBalancerUnsatError, ClaripyOperationError
from .operations import commutative_operations, opposites

l = logging.getLogger("claripy.balancer")


class Balancer:
    """
    The Balancer is an equation redistributor. The idea is to take an AST and rebalance it to, for example, isolate
    unknown terms on one side of an inequality.
    """

    def __init__(self, helper, c, validation_frontend=None):
        self._helper = helper
        self._validation_frontend = validation_frontend
        self._truisms = []
        self._processed_truisms = set()
        self._identified_assumptions = set()
        self._lower_bounds = {}
        self._upper_bounds = {}

        self._queue_truism(c.ite_excavated)

        self.sat = True
        try:
            self._doit()
        except ClaripyBalancerUnsatError:
            self.bounds = {}
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
            bound_si = BVS("bound", len(k.ast), min=mn, max=mx)
            l.debug("Yielding bound %s for %s.", bound_si, k.ast)
            if k.ast.op == "Reverse":
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
        return BVS("bounds", len(a), min=mn, max=mx, stride=si._stride)

    @staticmethod
    def _cardinality(a):
        return a.cardinality if isinstance(a, Base) else 0

    @staticmethod
    def _min(a, signed=False):
        converted = backends.vsa.convert(a)
        if isinstance(converted, vsa.ValueSet):
            if len(converted.regions) == 1:
                converted = next(iter(converted.regions.values()))
            else:
                # unfortunately, this is a real abstract pointer
                # the minimum value will be 0 or MIN_INT
                if signed:
                    return -(1 << (len(converted) - 1))
                return 0
        bounds = converted._unsigned_bounds() if not signed else converted._signed_bounds()
        return min(mn for mn, mx in bounds)

    @staticmethod
    def _max(a, signed=False):
        converted = backends.vsa.convert(a)
        if isinstance(converted, vsa.ValueSet):
            if len(converted.regions) == 1:
                converted = next(iter(converted.regions.values()))
            else:
                # unfortunately, this is a real abstract pointer
                # the minimum value will be 0 or MIN_INT
                if signed:
                    return (1 << (len(converted) - 1)) - 1
                return (1 << len(converted)) - 1
        bounds = converted._unsigned_bounds() if not signed else converted._signed_bounds()
        return max(mx for mn, mx in bounds)

    def _range(self, a, signed=False):
        return (self._min(a, signed=signed), self._max(a, signed=signed))

    @staticmethod
    def _invert_comparison(a):
        return claripy.Not(a)

    #
    # Truism alignment
    #

    def _align_truism(self, truism):
        outer_aligned = self._align_ast(truism)
        inner_aligned = outer_aligned.make_like(
            outer_aligned.op, (self._align_ast(outer_aligned.args[0]),) + outer_aligned.args[1:]
        )

        if not backends.vsa.identical(inner_aligned, truism):
            l.critical(
                "ERROR: the balancer is messing up an AST. This must be looked into. "
                "Please submit the binary and script to the angr project, if possible. "
                "Outer op is %s and inner op is %s.",
                truism.op,
                truism.args[0].op,
            )
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
            if isinstance(a, Bool) and len(a.args) == 2 and a.args[1].cardinality > a.args[0].cardinality:
                return self._reverse_comparison(a)
            return a
        except ClaripyBalancerError:
            return a

    @staticmethod
    def _reverse_comparison(a):
        try:
            new_op = opposites[a.op]
        except KeyError as err:
            raise ClaripyBalancerError(f"unable to reverse comparison {a.op} (missing from 'opposites')") from err

        try:
            op = getattr(operator, new_op)
        except AttributeError as err:
            raise ClaripyBalancerError(f"unable to reverse comparison {a.op} (AttributeError)") from err

        try:
            return op(*a.args[::-1])
        except ClaripyOperationError as err:
            # TODO: copy trace
            raise ClaripyBalancerError(f"unable to reverse comparison {a.op} (ClaripyOperationError)") from err

    def _align_bv(self, a):
        if a.op in commutative_operations:
            return a.make_like(a.op, tuple(sorted(a.args, key=lambda v: -self._cardinality(v))))
        try:
            op = getattr(self, "_align_" + a.op)
        except AttributeError:
            return a
        return op(a)

    def _align___sub__(self, a):
        cardinalities = [self._cardinality(v) for v in a.args]
        if max(cardinalities) == cardinalities[0]:
            return a

        adjusted = tuple(operator.__neg__(v) for v in a.args[1:]) + a.args[:1]
        return a.make_like("__add__", tuple(sorted(adjusted, key=lambda v: -self._cardinality(v))))

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
            if is_false(truism):
                raise ClaripyBalancerUnsatError

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
        if (not check_true) or (check_true and not is_true(t)):
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
            return None
        if t.args[0].cardinality > 1 and t.args[1].cardinality > 1:
            l.debug("can't do anything because we have multiple multivalued guys")
            return False
        if t.op == "If":
            l.debug("can't handle If")
            return False
        return True

    @staticmethod
    def _adjust_truism(t):
        """
        Swap the operands of the truism if the unknown variable is on the right side and the concrete value is on the
        left side.
        """
        if t.args[0].cardinality == 1 and t.args[1].cardinality > 1:
            return Balancer._reverse_comparison(t)
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

        if t.op in ("__le__", "__lt__", "ULE", "ULT"):
            return [t.args[0] >= 0]
        if t.op in ("__ge__", "__gt__", "UGE", "UGT"):
            return [t.args[0] <= 2 ** len(t.args[0]) - 1]
        if t.op in ("SLE", "SLT"):
            return [claripy.SGE(t.args[0], -(1 << (len(t.args[0]) - 1)))]
        if t.op in ("SGE", "SGT"):
            return [claripy.SLE(t.args[0], (1 << (len(t.args[0]) - 1)) - 1)]
        return []

    #
    # Truism extractor
    #

    def _unpack_truisms(self, c) -> set:
        """
        Given a constraint, _unpack_truisms() returns a set of constraints that must be True for
        this constraint to be True.
        """

        try:
            op = getattr(self, "_unpack_truisms_" + c.op)
        except AttributeError:
            return set()
        return op(c)

    def _unpack_truisms_And(self, c):
        return set.union(*[self._unpack_truisms(a) for a in c.args])

    def _unpack_truisms_Not(self, c):
        if c.args[0].op == "And":
            return self._unpack_truisms(claripy.Or(*[claripy.Not(a) for a in c.args[0].args]))
        if c.args[0].op == "Or":
            return self._unpack_truisms(claripy.And(*[claripy.Not(a) for a in c.args[0].args]))
        return set()

    def _unpack_truisms_Or(self, c):
        vals = [is_false(v) for v in c.args]
        if all(vals):
            raise ClaripyBalancerUnsatError
        if vals.count(False) == 1:
            return self._unpack_truisms(c.args[vals.index(False)])
        return set()

    #
    # Dealing with constraints
    #

    comparison_info = {}
    # Tuples look like (is_lt, is_eq, is_unsigned)
    comparison_info["SLT"] = (True, False, False)
    comparison_info["SLE"] = (True, True, False)
    comparison_info["SGT"] = (False, False, False)
    comparison_info["SGE"] = (False, True, False)
    comparison_info["ULT"] = (True, False, True)
    comparison_info["ULE"] = (True, True, True)
    comparison_info["UGT"] = (False, False, True)
    comparison_info["UGE"] = (False, True, True)
    comparison_info["__lt__"] = comparison_info["ULT"]
    comparison_info["__le__"] = comparison_info["ULE"]
    comparison_info["__gt__"] = comparison_info["UGT"]
    comparison_info["__ge__"] = comparison_info["UGE"]

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
                balancer = getattr(self, f"_balance_{inner_aligned.args[0].op}")
            except AttributeError:
                l.debug("Balance handler %s is not found in balancer. Consider implementing.", truism.args[0].op)
                return truism

            balanced = balancer(inner_aligned)
            if balanced is inner_aligned:
                return balanced
            return self._balance(balanced)
        except ClaripyBalancerError:
            l.warning("Balance handler for operation %s raised exception.", truism.args[0].op)
            return truism

    @staticmethod
    def _balance_Reverse(truism):
        if truism.op in ["__eq__", "__ne__"]:
            return truism.make_like(truism.op, (truism.args[0].args[0], truism.args[1].reversed))
        return truism

    @staticmethod
    def _balance___add__(truism):
        if len(truism.args) != 2:
            return truism
        new_lhs = truism.args[0].args[0]
        old_rhs = truism.args[1]
        other_adds = truism.args[0].args[1:]
        new_rhs = truism.args[0].make_like("__sub__", (old_rhs, *other_adds))
        return truism.make_like(truism.op, (new_lhs, new_rhs))

    @staticmethod
    def _balance___sub__(truism):
        if len(truism.args) != 2:
            return truism
        new_lhs = truism.args[0].args[0]
        old_rhs = truism.args[1]
        other_adds = truism.args[0].args[1:]
        new_rhs = truism.args[0].make_like("__add__", (old_rhs, *other_adds))
        return truism.make_like(truism.op, (new_lhs, new_rhs))

    @staticmethod
    def _balance_ZeroExt(truism):
        num_zeroes, inner = truism.args[0].args
        other_side = truism.args[1][len(truism.args[1]) - 1 : len(truism.args[1]) - num_zeroes]

        if is_true(other_side == 0):
            # We can safely eliminate this layer of ZeroExt
            new_args = (inner, truism.args[1][len(truism.args[1]) - num_zeroes - 1 : 0])
            return truism.make_like(truism.op, new_args)

        return truism

    @staticmethod
    def _balance_SignExt(truism):
        num_zeroes = truism.args[0].args[0]
        left_side = truism.args[0][len(truism.args[1]) - 1 : len(truism.args[1]) - num_zeroes]
        other_side = truism.args[1][len(truism.args[1]) - 1 : len(truism.args[1]) - num_zeroes]

        # TODO: what if this is a set value, but *not* the same as other_side
        if backends.vsa.identical(left_side, other_side):
            # We can safely eliminate this layer of ZeroExt
            new_args = (truism.args[0].args[1], truism.args[1][len(truism.args[1]) - num_zeroes - 1 : 0])
            return truism.make_like(truism.op, new_args)

        return truism

    @staticmethod
    def _balance_Extract(truism):
        high, low, inner = truism.args[0].args
        inner_size = len(inner)

        if high < inner_size - 1:
            left_msb = inner[inner_size - 1 : high + 1]
            left_msb_zero = is_true(left_msb == 0)
        else:
            left_msb = None
            left_msb_zero = None

        if low > 0:
            left_lsb = inner[high - 1 : 0]
            left_lsb_zero = is_true(left_lsb == 0)
        else:
            left_lsb = None
            left_lsb_zero = None

        if left_msb_zero and left_lsb_zero:
            new_left = inner
            new_right = claripy.Concat(BVV(0, len(left_msb)), truism.args[1], BVV(0, len(left_lsb)))
            return truism.make_like(truism.op, (new_left, new_right))
        if left_msb_zero:
            new_left = inner
            new_right = claripy.Concat(BVV(0, len(left_msb)), truism.args[1])
            return truism.make_like(truism.op, (new_left, new_right))
        if left_lsb_zero:
            new_left = inner
            new_right = claripy.Concat(truism.args[1], BVV(0, len(left_lsb)))
            return truism.make_like(truism.op, (new_left, new_right))

        if low == 0 and truism.args[1].op == "BVV" and truism.op not in {"SGE", "SLE", "SGT", "SLT"}:
            # single-valued rhs value with an unsigned operator
            # Eliminate Extract on lhs and zero-extend the value on rhs
            new_left = inner
            new_right = claripy.ZeroExt(inner.size() - truism.args[1].size(), truism.args[1])
            return truism.make_like(truism.op, (new_left, new_right))

        return truism

    @staticmethod
    def _balance___and__(truism):
        if len(truism.args[0].args) != 2:
            return truism
        op0, op1 = truism.args[0].args

        if op1.op == "BVV":
            # if all low bits of right are 1 and all high bits of right are 0, then this is equivalent to Extract()
            v = op1.args[0]
            low_ones = 0
            while v != 0:
                if v & 1 == 0:
                    # not all high bits are 0. abort
                    return truism
                low_ones += 1
                v >>= 1
            if low_ones == 0:
                # this should probably never happen
                new_left = truism.args[0].make_like("BVV", (0, truism.args[0].size()))
                return truism.make_like(truism.op, (new_left, truism.args[1]))

            if op0.op == "ZeroExt" and op0.args[0] + low_ones == op0.size():
                # ZeroExt(56, a) & 0xff == a  if a.size() == 8
                # we can safely remove __and__
                new_left = op0
                return truism.make_like(truism.op, (new_left, truism.args[1]))

        return truism

    @staticmethod
    def _balance_Concat(truism):
        size = len(truism.args[0])
        left_msb = truism.args[0].args[0]
        right_msb = truism.args[1][size - 1 : size - len(left_msb)]

        if is_true(left_msb == 0) and is_true(right_msb == 0):
            # we can cut these guys off!
            remaining_left = claripy.Concat(*truism.args[0].args[1:])
            remaining_right = truism.args[1][size - len(left_msb) - 1 : 0]
            return truism.make_like(truism.op, (remaining_left, remaining_right))
        # TODO: handle non-zero single-valued cases
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

        rhs_lower = claripy.Extract(shift_amount - 1, 0, rhs)
        rhs_lower_values = self._helper.eval(rhs_lower, 2)
        if len(rhs_lower_values) == 1 and rhs_lower_values[0] == 0:
            # we can remove the __lshift__

            return truism.make_like(truism.op, (expr, rhs >> shift_amount))

        return truism

    def _balance_If(self, truism):
        condition, true_expr, false_expr = truism.args[0].args

        try:
            if truism.op.startswith("__"):
                true_condition = getattr(operator, truism.op)(true_expr, truism.args[1])
                false_condition = getattr(operator, truism.op)(false_expr, truism.args[1])
            else:
                true_condition = getattr(claripy, truism.op)(true_expr, truism.args[1])
                false_condition = getattr(claripy, truism.op)(false_expr, truism.args[1])
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
        if not (can_true or can_false):
            # neither are satisfiable. This truism is fucked
            raise ClaripyBalancerUnsatError
        if must_true or (can_true and not can_false):
            # it will always be true
            self._queue_truism(condition)
            return truism.make_like(truism.op, (true_expr, truism.args[1]))
        if must_false or (can_false and not can_true):
            # it will always be false
            self._queue_truism(self._invert_comparison(condition))
            return truism.make_like(truism.op, (false_expr, truism.args[1]))
        return None

    #
    # Constraint handlers
    #

    def _handle(self, truism):
        l.debug("Handling %s", truism)

        if is_false(truism):
            raise ClaripyBalancerUnsatError
        if self._cardinality(truism.args[0]) == 1:
            # we are down to single-cardinality arguments, so our work is not
            # necessary
            return

        try:
            handler = getattr(self, f"_handle_{truism.op}")
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
        int_max = 2**size - 1 if is_unsigned else 2 ** (size - 1) - 1
        int_min = -(2 ** (size - 1))

        left_min = self._min(truism.args[0], signed=not is_unsigned)
        left_max = self._max(truism.args[0], signed=not is_unsigned)
        right_min = self._min(truism.args[1], signed=not is_unsigned)
        right_max = self._max(truism.args[1], signed=not is_unsigned)

        bound_max = right_max if is_equal else (right_max - 1 if is_lt else right_max + 1)
        bound_min = right_min if is_equal else (right_min - 1 if is_lt else right_min + 1)

        if is_lt and bound_max < int_min:
            # if the bound max is negative and we're unsigned less than, we're fucked
            raise ClaripyBalancerUnsatError
        if not is_lt and bound_min > int_max:
            # if the bound min is too big, we're fucked
            raise ClaripyBalancerUnsatError

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
                self._add_lower_bound(lhs, val + 1)
            elif val in (max_int, val - 1):
                self._add_upper_bound(lhs, max_int - 1)

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


def is_true(a):
    return backends.vsa.is_true(a)


def is_false(a):
    return backends.vsa.is_false(a)
