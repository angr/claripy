class ConstraintFixerMixin:
    def add(self, constraints, **kwargs):
        constraints = [ constraints ] if not isinstance(constraints, (list, tuple, set)) else constraints

        if len(constraints) == 0:
            return [ ]

        constraints = [ BoolV(c) if isinstance(c, bool) else c for c in constraints ]
        return super(ConstraintFixerMixin, self).add(constraints, **kwargs)

from .. import BoolV
