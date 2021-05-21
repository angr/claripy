#!/usr/bin/env python

import logging
l = logging.getLogger("claripy.frontends.light_frontend")

from .constrained_frontend import ConstrainedFrontend

class LightFrontend(ConstrainedFrontend):
    def __init__(self, solver_backend, **kwargs):
        # since the LightFrontend mostly cannot handle extra_constriants, it horribly misuses the cache.
        # Because of this, we have to disable the caching here.
        super().__init__(**kwargs)
        self._solver_backend = solver_backend

    def _blank_copy(self, c):
        super()._blank_copy(c)
        c._solver_backend = self._solver_backend

    def _copy(self, c):
        super()._copy(c)

    #
    # Serialization support
    #

    def __getstate__(self):
        return self._solver_backend.__class__.__name__, super().__getstate__()

    def __setstate__(self, s):
        solver_backend_name, base_state = s
        super().__setstate__(base_state)
        self._solver_backend = backends._backends_by_type[solver_backend_name]

    #
    # Light functionality
    #

    def eval(self, e, n, extra_constraints=(), exact=None):
        try:
            return tuple(self._solver_backend.eval(e, n))
        except BackendError as e:
            raise ClaripyFrontendError("Light solver can't handle this eval().") from e

    def batch_eval(self, exprs, n, extra_constraints=(), exact=None):
        try:
            return self._solver_backend._batch_eval(exprs, n)
        except BackendError as e:
            raise ClaripyFrontendError("Light solver can't handle this batch_eval().") from e

    def max(self, e, extra_constraints=(), signed=False, exact=None):
        try:
            return self._solver_backend.max(e, signed=signed)
        except BackendError as e:
            raise ClaripyFrontendError("Light solver can't handle this max().") from e

    def min(self, e, extra_constraints=(), signed=False, exact=None):
        try:
            return self._solver_backend.min(e, signed=signed)
        except BackendError as e:
            raise ClaripyFrontendError("Light solver can't handle this min().") from e

    def solution(self, e, v, extra_constraints=(), exact=None):
        try:
            return self._solver_backend.solution(e, v)
        except BackendError as e:
            raise ClaripyFrontendError("Light solver can't handle this solution().") from e

    def is_true(self, e, extra_constraints=(), exact=None):
        try:
            return self._solver_backend.is_true(e)
        except BackendError:
            l.info("Light solver can't handle this is_true().")
            return False

    def is_false(self, e, extra_constraints=(), exact=None):
        try:
            return self._solver_backend.is_false(e)
        except BackendError:
            l.info("Light solver can't handle this is_false().")
            return False

    def satisfiable(self, extra_constraints=(), exact=None):
        if any(
            self.is_false(c, extra_constraints=extra_constraints, exact=exact) for c in
            reversed(self.constraints + list(extra_constraints))
        ):
            return False
        else:
            return True

    #
    # Merging and splitting
    #

    def merge(self, others, merge_conditions, common_ancestor=None):
        return self._solver_backend.__class__.__name__ == 'BackendZ3', ConstrainedFrontend.merge(
            self, others, merge_conditions, common_ancestor=common_ancestor
        )[1]

from ..errors import BackendError, ClaripyFrontendError
from ..backend_manager import backends
