#!/usr/bin/env python

import logging
l = logging.getLogger("claripy.frontends.cache_mixin")

class CacheMixin(object):
    def __init__(self, *args, **kwargs):
        super(CacheMixin, self).__init__(*args, **kwargs)
        self.result = None
        self._cache = True

    def _blank_copy(self, c):
        super(CacheMixin, self)._blank_copy(c)
        c.result = None
        c._cache = self._cache

    def _copy(self, c):
        super(CacheMixin, self)._copy(c)
        c.result = self.result

    def _ana_getstate(self):
        return self.result, self._cache, super(CacheMixin, self)._ana_getstate()

    def _ana_setstate(self, s):
        self.result, self._cache, base_state = s
        super(CacheMixin, self)._ana_setstate(base_state)

    #
    # Caching
    #

    def _cache_eval(self, e, values, n=None, exact=None):
        if exact is False or not self._cache or self.result is None:
            return

        self.result.eval_cache[e.uuid] = self.result.eval_cache[e.uuid] | values if e.uuid in self.result.eval_cache else values
        if n is not None:
            self.result.eval_n[e.uuid] = max(n, self.result.eval_n[e.uuid]) if e.uuid in self.result.eval_n else n

    def _cache_max(self, e, m, exact=None):
        if exact is False or not self._cache or self.result is None:
            return

        self._cache_eval(e, {m}, exact=exact)
        self.result.max_cache[e.uuid] = min(self.result.max_cache.get(e, (2**e.length)-1), m)

    def _cache_min(self, e, m, exact=None):
        if exact is False or not self._cache or self.result is None:
            return

        self._cache_eval(e, {m}, exact=exact)
        self.result.min_cache[e.uuid] = max(self.result.min_cache.get(e, 0), m)

    #
    # Solving
    #

    def add(self, constraints, invalidate_cache=True, **kwargs):
        if len(constraints) == 0:
            return constraints

        added = super(CacheMixin, self).add(constraints, **kwargs)
        if invalidate_cache and self.result is not None and self.result.sat:
            self.result = None

        return added

    def solve(self, extra_constraints=(), exact=None, **kwargs):
        if self.result is not None and (not exact or not self.result.approximation):
            if not self.result.sat or len(extra_constraints) == 0:
                l.debug("... returning cached result (sat: %s)", self.result.sat)
                return self.result
        else:
            l.debug("... no cached result")

        r = super(CacheMixin, self).solve(extra_constraints=extra_constraints, exact=exact, **kwargs)
        if exact is not False and (len(extra_constraints) == 0 or (self.result is None and r.sat)):
            l.debug("... caching result (sat: %s)", r.sat)
            self.result = r
        return r

    def eval(self, e, n, extra_constraints=(), exact=None, **kwargs):
        # check the cache
        if len(extra_constraints) == 0 and self.result is not None and e.uuid in self.result.eval_cache:
            cached_results = self.result.eval_cache[e.uuid]
            cached_n = self.result.eval_n.get(e.uuid, 0)
        else:
            cached_results = frozenset()
            cached_n = 0

        # if there's enough in the cache, return that
        if cached_n >= n or len(cached_results) < cached_n or len(cached_results) >= n:
            return tuple(sorted(cached_results))[:n]

        # try to make sure we don't get more of the same
        solver_extra_constraints = list(extra_constraints) + [e != v for v in cached_results]

        # if we still need more results, get them from the frontend
        try:
            n_lacking = n - len(cached_results)
            eval_results = frozenset(
                super(CacheMixin, self).eval(
                    e, n_lacking,
                    extra_constraints=solver_extra_constraints,
                    exact=exact,
                    **kwargs
                )
            )
            l.debug("... got %d more values", len(eval_results))
        except UnsatError:
            l.debug("... UNSAT")
            if len(cached_results) == 0:
                raise
            else:
                eval_results = frozenset()

        # if, for some reason, we have no result object, make an approximate one
        if self.result is None:
            self.result = SatResult(approximation=True)

        # if there are less possible solutions than n (i.e., meaning we got all the solutions for e),
        # add constraints to help the solver out later
        # TODO: does this really help?
        all_results = cached_results | eval_results
        if len(extra_constraints) == 0 and len(all_results) < n:
            l.debug("... adding constraints for %d values for future speedup", len(all_results))
            self.add([Or(*[e == v for v in eval_results | cached_results])], invalidate_cache=False)

        # fix up the cache. If there were extra constraints, we can't assume that we got
        # all of the possible solutions, so we have to settle for a biggest-evaluated value
        # equal to the number of values we got
        self._cache_eval(e, all_results, n=n if len(extra_constraints) == 0 else None, exact=exact)

        # sort so the order of results is consistent when using pypy
        return tuple(sorted(all_results))

    def max(self, e, extra_constraints=(), exact=None, **kwargs):
        if len(extra_constraints) == 0 and self.result is not None and e.uuid in self.result.max_cache:
            #cached_max += 1
            return self.result.max_cache[e.uuid]

        m = super(CacheMixin, self).max(e, extra_constraints=extra_constraints, exact=exact, **kwargs)
        if len(extra_constraints) == 0 and e.symbolic:
            self._cache_max(e, m, exact=exact)
            self.add([e <= m], invalidate_cache=False)
        return m

    def min(self, e, extra_constraints=(), exact=None, **kwargs):
        if len(extra_constraints) == 0 and self.result is not None and e.uuid in self.result.min_cache:
            #cached_min += 1
            return self.result.min_cache[e.uuid]

        m = super(CacheMixin, self).min(e, extra_constraints=extra_constraints, exact=exact, **kwargs)
        if len(extra_constraints) == 0 and e.symbolic:
            self._cache_min(e, m, exact=exact)
            self.add([e >= m], invalidate_cache=False)
        return m

    def solution(self, e, v, extra_constraints=(), exact=None, **kwargs):
        b = super(CacheMixin, self).solution(
            e, v,
            extra_constraints=extra_constraints,
            exact=exact,
            **kwargs
        )
        if b is False and len(extra_constraints) == 0 and e.symbolic:
            self.add([e != v], invalidate_cache=False)

        # add these results to the cache
        if self.result is not None and b is True:
            if isinstance(e, Base) and e.symbolic and not isinstance(v, Base):
                self._cache_eval(e, frozenset({v}), exact=exact)
            if isinstance(v, Base) and v.symbolic and not isinstance(e, Base):
                self._cache_eval(v, frozenset({e}), exact=exact)

        return b

    #
    # Serialization and such.
    #

    def downsize(self): #pylint:disable=R0201
        if self.result is not None:
            self.result.downsize()
        super(CacheMixin, self).downsize()

from ..result import SatResult
from ..errors import UnsatError
from ..ast import Base
from ..ast.bool import Or
