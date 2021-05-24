#!/usr/bin/env python

import logging
l = logging.getLogger("claripy.frontends.cache_mixin")

class ConstraintExpansionMixin:
    def eval(self, e, n, extra_constraints=(), exact=None, **kwargs):
        results = super(ConstraintExpansionMixin, self).eval(
            e, n,
            extra_constraints=extra_constraints,
            exact=exact,
            **kwargs
        )

        # if there are less possible solutions than n (i.e., meaning we got all the solutions for e),
        # add constraints to help the solver out later
        # TODO: does this really help?
        if len(extra_constraints) == 0 and len(results) < n:
            self.add([Or(*[e == v for v in results])], invalidate_cache=False)

        return results

    def max(self, e, extra_constraints=(), exact=None, signed=False, **kwargs):
        m = super(ConstraintExpansionMixin, self).max(e, extra_constraints=extra_constraints, exact=exact,
                                                      signed=signed, **kwargs)
        if len(extra_constraints) == 0:
            self.add([SLE(e, m) if signed else ULE(e, m)], invalidate_cache=False)
        return m

    def min(self, e, extra_constraints=(), exact=None, signed=False, **kwargs):
        m = super(ConstraintExpansionMixin, self).min(e, extra_constraints=extra_constraints, exact=exact,
                                                      signed=signed, **kwargs)
        if len(extra_constraints) == 0:
            self.add([SGE(e, m) if signed else UGE(e, m)], invalidate_cache=False)
        return m

    def solution(self, e, v, extra_constraints=(), exact=None, **kwargs):
        b = super(ConstraintExpansionMixin, self).solution(
            e, v,
            extra_constraints=extra_constraints,
            exact=exact,
            **kwargs
        )
        if b is False and len(extra_constraints) == 0:
            self.add([e != v], invalidate_cache=False)
        return b

from ..ast.bool import Or
from ..ast.bv import SGE, SLE, UGE, ULE
