class ConstraintFilterMixin:
    def _constraint_filter(self, constraints, **kwargs):
        if type(constraints) not in (tuple, list):
            raise ClaripyValueError("The extra_constraints argument should be a list of constraints.")

        if len(constraints) == 0:
            return constraints

        filtered = super(ConstraintFilterMixin, self)._constraint_filter(constraints, **kwargs)
        ccs = [ self._concrete_constraint(c) for c in filtered ]
        if False in ccs:
            raise UnsatError("Constraints contain False.")
        else:
            return tuple((o if n is None else o) for o,n in zip(constraints, ccs) if n is not True)

    def add(self, constraints, **kwargs):
        try:
            ec = self._constraint_filter(constraints)
        except UnsatError:
            # filter out concrete False
            ec = list(c for c in constraints if c not in {False, false}) + [ false ]

        if len(constraints) == 0:
            return [ ]

        if len(ec) > 0:
            return super(ConstraintFilterMixin, self).add(ec, **kwargs)
        else:
            return [ ]

    def satisfiable(self, extra_constraints=(), **kwargs):
        try:
            ec = self._constraint_filter(extra_constraints)
            return super(ConstraintFilterMixin, self).satisfiable(extra_constraints=ec, **kwargs)
        except UnsatError:
            return False

    def eval(self, e, n, extra_constraints=(), **kwargs):
        ec = self._constraint_filter(extra_constraints)
        return super(ConstraintFilterMixin, self).eval(e, n, extra_constraints=ec, **kwargs)

    def batch_eval(self, exprs, n, extra_constraints=(), **kwargs):
        ec = self._constraint_filter(extra_constraints)
        return super(ConstraintFilterMixin, self).batch_eval(exprs, n, extra_constraints=ec, **kwargs)

    def max(self, e, extra_constraints=(), **kwargs):
        ec = self._constraint_filter(extra_constraints)
        return super(ConstraintFilterMixin, self).max(e, extra_constraints=ec, **kwargs)

    def min(self, e, extra_constraints=(), **kwargs):
        ec = self._constraint_filter(extra_constraints)
        return super(ConstraintFilterMixin, self).min(e, extra_constraints=ec, **kwargs)

    def solution(self, e, v, extra_constraints=(), **kwargs):
        ec = self._constraint_filter(extra_constraints)
        return super(ConstraintFilterMixin, self).solution(e, v, extra_constraints=ec, **kwargs)

    def is_true(self, e, extra_constraints=(), **kwargs):
        ec = self._constraint_filter(extra_constraints)
        return super(ConstraintFilterMixin, self).is_true(e, extra_constraints=ec, **kwargs)

    def is_false(self, e, extra_constraints=(), **kwargs):
        ec = self._constraint_filter(extra_constraints)
        return super(ConstraintFilterMixin, self).is_false(e, extra_constraints=ec, **kwargs)

from ..errors import UnsatError, ClaripyValueError
from .. import false
