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

        if _VALIDATE_BALANCER:
            approximate_frontend._validation_frontend = self._exact_frontend

    def _blank_copy(self, c):
        c._exact_frontend = self._exact_frontend.blank_copy()
        c._approximate_frontend = self._approximate_frontend.blank_copy()

        if _VALIDATE_BALANCER:
            c._approximate_frontend._validation_frontend = self._exact_frontend


    def _copy(self, c):
        self._exact_frontend._copy(c._exact_frontend)
        self._approximate_frontend._copy(c._approximate_frontend)

        if _VALIDATE_BALANCER:
            c._approximate_frontend._validation_frontend = self._exact_frontend

    #
    # Some passthroughs
    #

    @property
    def constraints(self):
        return self._exact_frontend.constraints

    @property
    def variables(self):
        return self._exact_frontend.variables

    #
    # Storable support
    #

    def _ana_getstate(self):
        return (self._exact_frontend, self._approximate_frontend, Frontend._ana_getstate(self))

    def _ana_setstate(self, s):
        self._exact_frontend, self._approximate_frontend, base_state = s
        Frontend._ana_setstate(self, base_state)

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

    def satisfiable(self, extra_constraints=(), exact=None):
        return self._hybrid_call('satisfiable', extra_constraints=extra_constraints, exact=exact)

    def eval_to_ast(self, e, n, extra_constraints=(), exact=None):
        return self._hybrid_call('eval_to_ast', e, n, extra_constraints=extra_constraints, exact=exact)

    def eval(self, e, n, extra_constraints=(), exact=None):
        return self._hybrid_call('eval', e, n, extra_constraints=extra_constraints, exact=exact)

    def batch_eval(self, e, n, extra_constraints=(), exact=None):
        return self._hybrid_call('batch_eval', e, n, extra_constraints=extra_constraints, exact=exact)

    def max(self, e, extra_constraints=(), exact=None):
        return self._hybrid_call('max', e, extra_constraints=extra_constraints, exact=exact)

    def min(self, e, extra_constraints=(), exact=None):
        return self._hybrid_call('min', e, extra_constraints=extra_constraints, exact=exact)

    def solution(self, e, v, extra_constraints=(), exact=None):
        return self._hybrid_call('solution', e, v, extra_constraints=extra_constraints, exact=exact)

    def is_true(self, e, extra_constraints=(), exact=None):
        return self._hybrid_call('is_true', e, extra_constraints=extra_constraints, exact=exact)

    def is_false(self, e, extra_constraints=(), exact=None):
        return self._hybrid_call('is_false', e, extra_constraints=extra_constraints, exact=exact)

    #
    # Lifecycle
    #

    def add(self, constraints):
        added = self._exact_frontend.add(constraints)
        self._approximate_frontend.add(constraints)
        return added

    def combine(self, others):
        other_exact = [o._exact_frontend for o in others]
        other_approximate = [o._approximate_frontend for o in others]
        new_exact = self._exact_frontend.combine(other_exact)
        new_approximate = self._approximate_frontend.combine(other_approximate)
        return HybridFrontend(new_exact, new_approximate)

    def merge(self, others, merge_conditions):
        other_exact = [o._exact_frontend for o in others]
        other_approximate = [o._approximate_frontend for o in others]
        e_merged, new_exact = self._exact_frontend.merge(other_exact, merge_conditions)
        new_approximate = self._approximate_frontend.merge(other_approximate, merge_conditions)[-1]
        return (e_merged, HybridFrontend(new_exact, new_approximate))

    def simplify(self):
        self._approximate_frontend.simplify()
        return self._exact_frontend.simplify()

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
            a = self._approximate_frontend.blank_copy()
            a.add(e.constraints)
            results.append(HybridFrontend(e, a))
        return results


from ..errors import ClaripyFrontendError
