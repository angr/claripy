#!/usr/bin/env python

import logging
l = logging.getLogger("claripy.frontends.light_frontend")

from .constrained_frontend import ConstrainedFrontend

class LightFrontend(ConstrainedFrontend):
    def __init__(self, solver_backend, **kwargs):
        # since the LightFrontend mostly cannot handle extra_constriants, it horribly misuses the cache.
        # Because of this, we have to disable the caching here.
        super(LightFrontend, self).__init__(**kwargs)
        self._solver_backend = solver_backend

    def _blank_copy(self, c):
        super(LightFrontend, self)._blank_copy(c)
        c._solver_backend = self._solver_backend

    def _copy(self, c):
        super(LightFrontend, self)._copy(c)

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

    def eval(self, e, n, extra_constraints=(), exact=None):
        try:
            return self._solver_backend.eval(e, n)
        except BackendError:
            raise ClaripyFrontendError("Light solver can't handle this eval().")

    def batch_eval(self, exprs, n, extra_constraints=(), exact=None):
        try:
            return self._solver_backend._batch_eval(exprs, n)
        except BackendError:
            raise ClaripyFrontendError("Light solver can't handle this batch_eval().")

    def max(self, e, extra_constraints=(), exact=None):
        try:
            return self._solver_backend.max(e)
        except BackendError:
            raise ClaripyFrontendError("Light solver can't handle this max().")

    def min(self, e, extra_constraints=(), exact=None):
        try:
            return self._solver_backend.min(e)
        except BackendError:
            raise ClaripyFrontendError("Light solver can't handle this min().")

    def solution(self, e, v, extra_constraints=(), exact=None):
        try:
            return self._solver_backend.solution(e, v)
        except BackendError:
            raise ClaripyFrontendError("Light solver can't handle this solution().")

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
            self._solver_backend.is_false(c) for c in
            reversed(self.constraints + list(extra_constraints))
        ):
            return False
        else:
            return True

    #
    # Merging and splitting
    #

    def merge(self, others, merge_conditions):
        return self._solver_backend.__class__.__name__ == 'BackendZ3', ConstrainedFrontend.merge(
            self, others, merge_conditions
        )[1]

from ..errors import BackendError, ClaripyFrontendError
from ..backend_manager import backends
