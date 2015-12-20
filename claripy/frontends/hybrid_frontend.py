#!/usr/bin/env python

import logging
l = logging.getLogger("claripy.frontends.hybrid_frontend")

from .full_frontend import FullFrontend
from .light_frontend import LightFrontend
from .replacement_frontend import ReplacementFrontend

class HybridFrontend(FullFrontend):
    def __init__(self, solver_backend, approximation_frontend=None, **kwargs):
        FullFrontend.__init__(self, solver_backend, **kwargs)
        self._approximation_frontend = approximation_frontend if approximation_frontend is not None else ReplacementFrontend(LightFrontend(backends.vsa), replace_constraints=True)

    #
    # Storable support
    #

    def _ana_getstate(self):
        return (self._approximation_frontend, FullFrontend._ana_getstate(self))

    def _ana_setstate(self, s):
        self._approximation_frontend, full_state = s
        FullFrontend._ana_setstate(self, full_state)

    def _blank_copy(self):
        return HybridFrontend(self._solver_backend, approximation_frontend=self._approximation_frontend._blank_copy(), cache=self._cache, timeout=self.timeout)

    def branch(self):
        s = super(HybridFrontend, self).branch()
        s._approximation_frontend = self._approximation_frontend.branch()
        return s

    #
    # Catch constraint adds and pass them to the replacement frontend
    #

    def _add_constraints(self, constraints, invalidate_cache=True):
        super(HybridFrontend, self)._add_constraints(constraints, invalidate_cache=invalidate_cache)
        self._approximation_frontend.add(constraints, invalidate_cache=invalidate_cache)

    def _cache_eval(self, e, values, n=None, exact=None, cache=None):
        super(HybridFrontend, self)._cache_eval(e, values, n=None, exact=exact, cache=cache)

        if not exact is False:
            if n > 1 and len(values) == 1:
                self._approximation_frontend.add_replacement(e, next(iter(values)))

    def _cache_max(self, e, mx, exact=None, cache=None):
        super(HybridFrontend, self)._cache_max(e, mx, exact=exact, cache=cache)

        if not exact is False and not cache is False:
            if isinstance(e, BV):
                try:
                    if self.result and e.uuid in self.result.min_cache:
                        mn = self.result.min_cache[e.uuid]
                    else:
                        mn = self._approximation_frontend.min(e)
                except ClaripyFrontendError:
                    mn = 0

                si = BVS('limiter', e.length, max=mx, min=mn)
                self._approximation_frontend.add_replacement(e, e.intersection(si))

    def _cache_min(self, e, mn, exact=None, cache=None):
        super(HybridFrontend, self)._cache_min(e, mn, exact=exact, cache=cache)

        if not exact is False and not cache is False:
            if isinstance(e, BV):
                try:
                    if self.result and e.uuid in self.result.max_cache:
                        mx = self.result.max_cache[e.uuid]
                    else:
                        mx = self._approximation_frontend.max(e)
                except ClaripyFrontendError:
                    mx = 0

                si = BVS('limiter', e.length, min=mn, max=mx)
                self._approximation_frontend.add_replacement(e, e.intersection(si))

    #
    # Hybrid solving
    #

    def _solve(self, extra_constraints=(), exact=None, cache=None):
        # if approximating, try the approximation backend
        if exact is False:
            try:
                return self._approximation_frontend.solve(extra_constraints=extra_constraints)
            except ClaripyFrontendError:
                l.debug("Approximation failed. Falling back on exact _solve()")

        # if that fails, try the exact backend
        return super(HybridFrontend, self)._solve(extra_constraints=extra_constraints, exact=exact, cache=cache)

    def _eval(self, e, n, extra_constraints=(), exact=None, cache=None):
        # if approximating, try the approximation backend
        if exact is False:
            try:
                return self._approximation_frontend.eval(e, n, extra_constraints=extra_constraints, cache=cache)
            except ClaripyFrontendError:
                l.debug("Approximation failed. Falling back on exact _eval()")

        # if that fails, try the exact backend
        return super(HybridFrontend, self)._eval(e, n, extra_constraints=extra_constraints, exact=exact, cache=cache)

    def _batch_eval(self, exprs, n, extra_constraints=(), exact=None, cache=None):

        if exact is False:
            try:
                return self._approximation_frontend.batch_eval(exprs, n, extra_constraints=extra_constraints)

            except ClaripyFrontendError:
                l.debug("Approximation failed. Falling back on exact _batch_eval()")

        return super(HybridFrontend, self)._batch_eval(
                exprs,
                n,
                extra_constraints=extra_constraints,
                exact=exact,
                cache=cache
        )

    def _max(self, e, extra_constraints=(), exact=None, cache=None):
        # if approximating, try the approximation backend
        if exact is False:
            try:
                return self._approximation_frontend.max(e, extra_constraints=extra_constraints, cache=cache)
            except ClaripyFrontendError:
                l.debug("Approximation failed. Falling back on exact _max()")

        # if that fails, try the exact backend
        return super(HybridFrontend, self)._max(e, extra_constraints=extra_constraints, exact=exact, cache=cache)

    def _min(self, e, extra_constraints=(), exact=None, cache=None):
        # if approximating, try the approximation backend
        if exact is False:
            try:
                return self._approximation_frontend.min(e, extra_constraints=extra_constraints, cache=cache)
            except ClaripyFrontendError:
                l.debug("Approximation failed. Falling back on exact _min()")

        # if that fails, try the exact backend
        return super(HybridFrontend, self)._min(e, extra_constraints=extra_constraints, exact=exact, cache=cache)

    def _solution(self, e, v, extra_constraints=(), exact=None, cache=None):
        # if approximating, try the approximation backend
        if exact is False:
            try:
                return self._approximation_frontend.solution(e, v, extra_constraints=extra_constraints, cache=cache)
            except ClaripyFrontendError:
                l.debug("Approximation failed. Falling back on exact _solution()")

        # if that fails, try the exact backend
        return super(HybridFrontend, self)._solution(e, v, extra_constraints=extra_constraints, exact=exact, cache=cache)

    def _is_true(self, e, extra_constraints=(), exact=None, cache=None):
        # if approximating, try the approximation backend
        if exact is False:
            try:
                return self._approximation_frontend.is_true(e, extra_constraints=extra_constraints, cache=cache)
            except ClaripyFrontendError:
                l.debug("Approximation failed. Falling back on exact _is_true()")

        # if that fails, try the exact backend
        return super(HybridFrontend, self)._is_true(e, extra_constraints=extra_constraints, exact=exact, cache=cache)

    def _is_false(self, e, extra_constraints=(), exact=None, cache=None):
        # if approximating, try the approximation backend
        if exact is False:
            try:
                return self._approximation_frontend.is_false(e, extra_constraints=extra_constraints, cache=cache)
            except ClaripyFrontendError:
                l.debug("Approximation failed. Falling back on exact _is_false()")

        # if that fails, try the exact backend
        return super(HybridFrontend, self)._is_false(e, extra_constraints=extra_constraints, exact=exact, cache=cache)

    def _satisfiable(self, extra_constraints=(), exact=None, cache=None):
        if exact is False:
            try:
                new_constraints = self._approximation_frontend._replace_list(self._approximation_frontend.constraints)
                self._approximation_frontend.constraints[:] = new_constraints
                return self._approximation_frontend.satisfiable(extra_constraints=extra_constraints, cache=cache)
            except ClaripyFrontendError:
                l.debug("Approximation failed. Falling back on exact _satisfiable()")

        # if that fails, try the exact backend
        return super(HybridFrontend, self)._satisfiable(extra_constraints=extra_constraints, exact=exact, cache=cache)


from ..errors import ClaripyFrontendError
from ..backend_manager import backends
from ..ast.bv import BV, BVS
