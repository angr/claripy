from __future__ import annotations

import logging

from claripy.ast.bool import Or
from claripy.ast.bv import SGE, SLE, UGE, ULE

l = logging.getLogger("claripy.frontends.cache_mixin")


class ConstraintExpansionMixin:
    def eval(self, e, n, extra_constraints=(), exact=None):
        results = super().eval(e, n, extra_constraints=extra_constraints, exact=exact)

        # if there are less possible solutions than n (i.e., meaning we got all the solutions for e),
        # add constraints to help the solver out later
        # TODO: does this really help?
        if len(extra_constraints) == 0 and len(results) < n:
            self.add([Or(*[e == v for v in results])], invalidate_cache=False)

        return results

    def max(self, e, extra_constraints=(), signed=False, exact=None):
        m = super().max(e, extra_constraints=extra_constraints, signed=signed, exact=exact)
        if len(extra_constraints) == 0:
            self.add([SLE(e, m) if signed else ULE(e, m)], invalidate_cache=False)
        return m

    def min(self, e, extra_constraints=(), signed=False, exact=None):
        m = super().min(e, extra_constraints=extra_constraints, signed=signed, exact=exact)
        if len(extra_constraints) == 0:
            self.add([SGE(e, m) if signed else UGE(e, m)], invalidate_cache=False)
        return m

    def solution(self, e, v, extra_constraints=(), exact=None):
        b = super().solution(e, v, extra_constraints=extra_constraints, exact=exact)
        if b is False and len(extra_constraints) == 0:
            self.add([e != v], invalidate_cache=False)
        return b
