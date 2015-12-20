#!/usr/bin/env python

import logging
l = logging.getLogger("claripy.frontends.light_frontend")

from .constrained_frontend import ConstrainedFrontend

class LightFrontend(ConstrainedFrontend):
    def __init__(self, solver_backend, cache=None, **kwargs):
        # since the LightFrontend mostly cannot handle extra_constriants, it horribly misuses the cache.
        # Because of this, we have to disable the caching here.
        ConstrainedFrontend.__init__(self, cache=False if cache is None else cache, **kwargs)
        self._solver_backend = solver_backend

    #
    # Storable support
    #

    def _ana_getstate(self):
        return self._solver_backend.__class__.__name__, ConstrainedFrontend._ana_getstate(self)

    def _ana_setstate(self, s):
        solver_backend_name, base_state = s
        ConstrainedFrontend._ana_setstate(self, base_state)
        self._solver_backend = backends._backends_by_type[solver_backend_name]

    #
    # Light functionality
    #

    def _eval(self, e, n, extra_constraints=(), exact=None, cache=None):
        try:
            return self._solver_backend.eval(e, n, result=self.result)
        except BackendError:
            raise ClaripyFrontendError("Light solver can't handle this eval().")

    def _batch_eval(self, exprs, n, extra_constraints=(), exact=None, cache=None):
        try:
            return self._solver_backend._batch_eval(exprs, n, result=self.result)
        except BackendError:
            raise ClaripyFrontendError("Light solver can't handle this batch_eval().")

    def _max(self, e, extra_constraints=(), exact=None, cache=None):
        try:
            return self._solver_backend.max(e, result=self.result)
        except BackendError:
            raise ClaripyFrontendError("Light solver can't handle this max().")

    def _min(self, e, extra_constraints=(), exact=None, cache=None):
        try:
            return self._solver_backend.min(e, result=self.result)
        except BackendError:
            raise ClaripyFrontendError("Light solver can't handle this min().")

    def _solution(self, e, v, extra_constraints=(), exact=None, cache=None):
        try:
            return self._solver_backend.solution(e, v, result=self.result)
        except BackendError:
            raise ClaripyFrontendError("Light solver can't handle this solution().")

    def _is_true(self, e, extra_constraints=(), exact=None, cache=None):
        try:
            return self._solver_backend.is_true(e, result=self.result)
        except BackendError:
            raise ClaripyFrontendError("Light solver can't handle this is_false().")

    def _is_false(self, e, extra_constraints=(), exact=None, cache=None):
        try:
            return self._solver_backend.is_false(e, result=self.result)
        except BackendError:
            raise ClaripyFrontendError("Light solver can't handle this is_false().")

    def _satisfiable(self, extra_constraints=(), exact=None, cache=None):
        try:
            return any(self._solver_backend.is_false(c) for c in reversed(self.constraints + list(extra_constraints)))
        except BackendError:
            raise ClaripyFrontendError("Light solver can't handle this is_false().")

    #
    # Merging and splitting
    #

    def _blank_copy(self):
        return LightFrontend(self._solver_backend, cache=self._cache)

    def merge(self, others, merge_flag, merge_values):
        return self._solver_backend.__class__.__name__ == 'BackendZ3', ConstrainedFrontend.merge(self, others, merge_flag, merge_values)[1]

from ..errors import BackendError, ClaripyFrontendError
from ..backend_manager import backends
