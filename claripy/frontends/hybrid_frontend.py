#!/usr/bin/env python

import logging
l = logging.getLogger("claripy.frontends.full_frontend")

from .full_frontend import FullFrontend

class HybridFrontend(FullFrontend):
    def __init__(self, solver_backend, approximation_backend=None, **kwargs):
        FullFrontend.__init__(self, solver_backend, **kwargs)
        self._approximation_backend = approximation_backend if approximation_backend is not None else _backends['BackendVSA']

    #
    # Storable support
    #

    def _ana_getstate(self):
        return (self._approximation_backend, FullFrontend._ana_getstate(self))

    def _ana_setstate(self, s):
        self._approximation_backend, full_state = s
        FullFrontend._ana_setstate(self, full_state)

    #
    # Hybrid solving
    #

    def _solve(self, extra_constraints=(), exact=None, cache=None):
        # if approximating, try the approximation backend
        if exact is False:
            try: return self._approximation_backend.solve(extra_constraints=extra_constraints)
            except BackendError: pass

        # if that fails, try the exact backend
        return super(HybridFrontend, self)._solve(extra_constraints=extra_constraints, exact=exact, cache=cache)

    def _eval(self, e, n, extra_constraints=(), exact=None, cache=None):
        # if approximating, try the approximation backend
        if exact is False:
            try: return self._approximation_backend.eval(e, n, extra_constraints=extra_constraints)
            except BackendError: pass

        # if that fails, try the exact backend
        return super(HybridFrontend, self)._eval(e, n, extra_constraints=extra_constraints, exact=exact, cache=cache)

    def _max(self, e, extra_constraints=(), exact=None, cache=None):
        # if approximating, try the approximation backend
        if exact is False:
            try: return self._approximation_backend.max(e, extra_constraints=extra_constraints)
            except BackendError: pass

        # if that fails, try the exact backend
        return super(HybridFrontend, self)._max(e, extra_constraints=extra_constraints, exact=exact, cache=cache)

    def _min(self, e, extra_constraints=(), exact=None, cache=None):
        # if approximating, try the approximation backend
        if exact is False:
            try: return self._approximation_backend.min(e, extra_constraints=extra_constraints)
            except BackendError: pass

        # if that fails, try the exact backend
        return super(HybridFrontend, self)._min(e, extra_constraints=extra_constraints, exact=exact, cache=cache)

    def _solution(self, e, v, extra_constraints=(), exact=None, cache=None):
        # if approximating, try the approximation backend
        if exact is False:
            try: return self._approximation_backend.solution(e, v, extra_constraints=extra_constraints)
            except BackendError: pass

        # if that fails, try the exact backend
        return super(HybridFrontend, self)._solution(e, v, extra_constraints=extra_constraints, exact=exact, cache=cache)

from ..errors import BackendError
from .. import _backends
