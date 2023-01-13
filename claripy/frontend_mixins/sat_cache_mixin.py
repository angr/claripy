class SatCacheMixin:
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._cached_satness = None

    def _blank_copy(self, c):
        super()._blank_copy(c)
        c._cached_satness = None

    def _copy(self, c):
        super()._copy(c)
        c._cached_satness = self._cached_satness

    def __getstate__(self):
        return self._cached_satness, super().__getstate__()

    def __setstate__(self, s):
        self._cached_satness, base_state = s
        super().__setstate__(base_state)

    #
    # SAT caching
    #

    def add(self, constraints, **kwargs):
        added = super().add(constraints, **kwargs)
        if len(added) > 0 and any(c is false for c in added):
            self._cached_satness = False
        elif self._cached_satness is True:
            self._cached_satness = None
        return added

    def simplify(self):
        new_constraints = super().simplify()
        if len(new_constraints) > 0 and any(c is false for c in new_constraints):
            self._cached_satness = False
        return new_constraints

    def satisfiable(self, extra_constraints=(), **kwargs):
        if self._cached_satness is False:
            return False
        if self._cached_satness is True and len(extra_constraints) == 0:
            return True
        r = super().satisfiable(extra_constraints=extra_constraints, **kwargs)
        if len(extra_constraints) == 0:
            self._cached_satness = r
        return r

    def eval(self, e, n, extra_constraints=(), **kwargs):
        if self._cached_satness is False:
            raise UnsatError("cached unsat")
        try:
            r = super().eval(e, n, extra_constraints=extra_constraints, **kwargs)
            self._cached_satness = True
            return r
        except UnsatError:
            if len(extra_constraints) == 0:
                self._cached_satness = False
            raise

    def batch_eval(self, e, n, extra_constraints=(), **kwargs):
        if self._cached_satness is False:
            raise UnsatError("cached unsat")
        try:
            r = super().batch_eval(e, n, extra_constraints=extra_constraints, **kwargs)
            self._cached_satness = True
            return r
        except UnsatError:
            if len(extra_constraints) == 0:
                self._cached_satness = False
            raise

    def max(self, e, extra_constraints=(), **kwargs):
        if self._cached_satness is False:
            raise UnsatError("cached unsat")
        try:
            r = super().max(e, extra_constraints=extra_constraints, **kwargs)
            self._cached_satness = True
            return r
        except UnsatError:
            if len(extra_constraints) == 0:
                self._cached_satness = False
            raise

    def min(self, e, extra_constraints=(), **kwargs):
        if self._cached_satness is False:
            raise UnsatError("cached unsat")
        try:
            r = super().min(e, extra_constraints=extra_constraints, **kwargs)
            self._cached_satness = True
            return r
        except UnsatError:
            if len(extra_constraints) == 0:
                self._cached_satness = False
            raise

    def solution(self, e, v, extra_constraints=(), **kwargs):
        if self._cached_satness is False:
            raise UnsatError("cached unsat")
        try:
            r = super().solution(e, v, extra_constraints=extra_constraints, **kwargs)
            self._cached_satness = True
            return r
        except UnsatError:
            if len(extra_constraints) == 0:
                self._cached_satness = False
            raise


from .. import false
from ..errors import UnsatError
