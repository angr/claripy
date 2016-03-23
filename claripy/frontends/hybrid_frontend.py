#!/usr/bin/env python

import logging

l = logging.getLogger("claripy.frontends.full_frontend")

from ..frontend import Frontend

_VALIDATE_BALANCER=False

class HybridFrontend(Frontend):
    def __init__(self, exact_frontend, approximate_frontend, **kwargs):
        Frontend.__init__(self, **kwargs)
        self._exact_frontend = exact_frontend
        self._approximate_frontend = approximate_frontend
        self._hook_exact_frontend()

        if _VALIDATE_BALANCER:
            approximate_frontend._validation_frontend = self._exact_frontend

    #
    # Some passthroughs
    #

    @property
    def constraints(self):
        return self._exact_frontend.constraints

    @property
    def variables(self):
        return self._exact_frontend.variables

    @property
    def result(self):
        return self._exact_frontend.result

    @result.setter
    def result(self, v):
        self._exact_frontend.result = v

    #
    # Storable support
    #

    def _hook_exact_frontend(self):
        def constraint_hook(constraints, **kwargs):
            self._exact_frontend._real_add_constraints(constraints, **kwargs)
            self._approximate_frontend._add_constraints(constraints, **kwargs)

        self._exact_frontend._real_add_constraints = self._exact_frontend._add_constraints
        self._exact_frontend._add_constraints = constraint_hook

    def _ana_getstate(self):
        return (self._exact_frontend, self._approximate_frontend, Frontend._ana_getstate(self))

    def _ana_setstate(self, s):
        self._exact_frontend, self._approximate_frontend, base_state = s
        Frontend._ana_setstate(self, base_state)

    def _blank_copy(self):
        return HybridFrontend(self._exact_frontend._blank_copy(), self._approximate_frontend._blank_copy())

    def branch(self):
        return HybridFrontend(self._exact_frontend.branch(), self._approximate_frontend.branch())

    #
    # Hybrid solving
    #

    def _hybrid_call(self, f_name, *args, **kwargs):
        exact = kwargs.pop('exact', True)

        # if approximating, try the approximation backend
        if exact is False:
            try:
                return getattr(self._approximate_frontend, f_name)(*args, **kwargs)
            except ClaripyFrontendError:
                pass

        # if that fails, try the exact backend
        return getattr(self._exact_frontend, f_name)(*args, **kwargs)

    def solve(self, extra_constraints=(), exact=None, cache=None):
        return self._hybrid_call('solve', extra_constraints=extra_constraints, exact=exact, cache=cache)

    def satisfiable(self, extra_constraints=(), exact=None, cache=None):
        return self._hybrid_call('satisfiable', extra_constraints=extra_constraints, exact=exact, cache=cache)

    def eval_to_ast(self, e, n, extra_constraints=(), exact=None, cache=None):
        return self._hybrid_call('eval_to_ast', e, n, extra_constraints=extra_constraints, exact=exact, cache=cache)

    def eval(self, e, n, extra_constraints=(), exact=None, cache=None):
        return self._hybrid_call('eval', e, n, extra_constraints=extra_constraints, exact=exact, cache=cache)

    def batch_eval(self, e, n, extra_constraints=(), exact=None, cache=None):
        return self._hybrid_call('batch_eval', e, n, extra_constraints=extra_constraints, exact=exact, cache=cache)

    def max(self, e, extra_constraints=(), exact=None, cache=None):
        return self._hybrid_call('max', e, extra_constraints=extra_constraints, exact=exact, cache=cache)

    def min(self, e, extra_constraints=(), exact=None, cache=None):
        return self._hybrid_call('min', e, extra_constraints=extra_constraints, exact=exact, cache=cache)

    def solution(self, e, v, extra_constraints=(), exact=None, cache=None):
        return self._hybrid_call('solution', e, v, extra_constraints=extra_constraints, exact=exact, cache=cache)

    def is_true(self, e, extra_constraints=(), exact=None, cache=None):
        return self._hybrid_call('is_true', e, extra_constraints=extra_constraints, exact=exact, cache=cache)

    def is_false(self, e, extra_constraints=(), exact=None, cache=None):
        return self._hybrid_call('is_false', e, extra_constraints=extra_constraints, exact=exact, cache=cache)

    #
    # Lifecycle
    #

    def add(self, constraints, invalidate_cache=True):
        self._exact_frontend.add(constraints, invalidate_cache=invalidate_cache)
        #self._approximate_frontend.add(constraints, invalidate_cache=invalidate_cache)

    def combine(self, others):
        other_exact = [o._exact_frontend for o in others]
        other_approximate = [o._approximate_frontend for o in others]
        new_exact = self._exact_frontend.combine(other_exact)
        new_approximate = self._approximate_frontend.combine(other_approximate)
        return HybridFrontend(new_exact, new_approximate)

    def merge(self, others, merge_flag, merge_values):
        other_exact = [o._exact_frontend for o in others]
        other_approximate = [o._approximate_frontend for o in others]
        e_merged, new_exact = self._exact_frontend.merge(other_exact, merge_flag, merge_values)
        new_approximate = self._approximate_frontend.merge(other_approximate, merge_flag, merge_values)[-1]
        return (e_merged, HybridFrontend(new_exact, new_approximate))

    def simplify(self):
        self._exact_frontend.simplify()
        self._approximate_frontend.simplify()

    def downsize(self):
        self._exact_frontend.downsize()
        self._approximate_frontend.downsize()

    def finalize(self):
        self._exact_frontend.finalize()
        self._approximate_frontend.finalize()

    def split(self):
        results = []
        exacts = self._exact_frontend.split()

        for e in exacts:
            a = self._approximate_frontend._blank_copy()
            a.add(e.constraints)
            results.append(HybridFrontend(e, a))
        return results


def hybrid_vsa_z3():
    return HybridFrontend(FullFrontend(backends.z3),
                          ReplacementFrontend(LightFrontend(backends.vsa), replace_constraints=True,
                                              complex_auto_replace=True))


from .full_frontend import FullFrontend
from .light_frontend import LightFrontend
from .replacement_frontend import ReplacementFrontend
from ..backend_manager import backends
from ..errors import ClaripyFrontendError
