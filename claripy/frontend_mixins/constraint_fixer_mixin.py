from claripy import BoolV


class ConstraintFixerMixin:
    def add(self, constraints, invalidate_cache=True):
        constraints = [constraints] if not isinstance(constraints, list | tuple | set) else constraints

        if len(constraints) == 0:
            return []

        constraints = [BoolV(c) if isinstance(c, bool) else c for c in constraints]
        return super().add(constraints, invalidate_cache=invalidate_cache)
