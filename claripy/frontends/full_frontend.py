#!/usr/bin/env python

import logging
l = logging.getLogger("claripy.frontends.full_frontend")

import sys
import threading

from .constrained_frontend import ConstrainedFrontend

class FullFrontend(ConstrainedFrontend):
    def __init__(self, solver_backend, timeout=None, **kwargs):
        ConstrainedFrontend.__init__(self, **kwargs)
        self._solver_backend = solver_backend
        self.timeout = timeout if timeout is not None else 300000
        self._tls = threading.local()
        self._to_add = [ ]

    #
    # Storable support
    #

    def _ana_getstate(self):
        return self._solver_backend.__class__.__name__, self.timeout, ConstrainedFrontend._ana_getstate(self)

    def _ana_setstate(self, s):
        backend_name, self.timeout, base_state = s
        self._solver_backend = backends._backends_by_type[backend_name]
        #self._tls = None
        self._tls = threading.local()
        self._to_add = [ ]
        ConstrainedFrontend._ana_setstate(self, base_state)

    #
    # Frontend Creation
    #

    def _get_solver(self):
        if getattr(self._tls, 'solver', None) is None or (self._finalized and len(self._to_add) > 0):
            self._tls.solver = self._solver_backend.solver(timeout=self.timeout)
            self._solver_backend.add(self._tls.solver, self.constraints)
            self._to_add = [ ]

        if len(self._to_add) > 0:
            self._solver_backend.add(self._tls.solver, self._to_add)
            self._to_add = [ ]

        return self._tls.solver

    #
    # Constraint management
    #

    def _add_constraints(self, constraints, invalidate_cache=True):
        to_add = ConstrainedFrontend._add_constraints(self, constraints, invalidate_cache=invalidate_cache)
        self._to_add += to_add
        return to_add

    def _simplify(self):
        ConstrainedFrontend._simplify(self)

        # TODO: should we do this?
        self._tls.solver = None
        self._to_add = [ ]
        self._simplified = True

        return self.constraints

    def _solve(self, extra_constraints=(), exact=None, cache=None):
        r = ConstrainedFrontend._solve(self, extra_constraints=extra_constraints)
        if not r.approximation:
            return r

        l.debug("Frontend.solve() checking SATness of %d constraints", len(self.constraints))

        try:
            s = self._get_solver()

            #a = time.time()
            r = self._solver_backend.results(s, extra_constraints, generic_model=True)
            #b = time.time()
            #l_timing.debug("... %s in %s seconds", r.sat, b - a)
            return r
        except BackendError:
            e_type, value, traceback = sys.exc_info()
            raise ClaripyFrontendError, "Backend error during solve: %s('%s')" % (str(e_type), str(value)), traceback

    def _eval(self, e, n, extra_constraints=(), exact=None, cache=None):
        if not self.satisfiable(extra_constraints=extra_constraints):
            raise UnsatError('unsat')

        return self._solver_backend.eval(e, n, extra_constraints=extra_constraints, result=self.result, solver=self._get_solver())

    def _batch_eval(self, exprs, n, extra_constraints=(), exact=None, cache=None):
        if not self.satisfiable(extra_constraints=extra_constraints):
            raise UnsatError('unsat')

        return self._solver_backend.batch_eval(
                exprs,
                n,
                extra_constraints=extra_constraints,
                result=self.result,
                solver=self._get_solver()
        )

    def _max(self, e, extra_constraints=(), exact=None, cache=None):
        if not self.satisfiable(extra_constraints=extra_constraints):
            raise UnsatError("Unsat during _max()")

        l.debug("Frontend.max() with %d extra_constraints", len(extra_constraints))

        two = self.eval(e, 2, extra_constraints=extra_constraints)
        if len(two) == 0: raise UnsatError("unsat during max()")
        elif len(two) == 1: return two[0]

        self.simplify()

        c = extra_constraints + (UGE(e, two[0]), UGE(e, two[1]))
        try:
            vals = self._solver_backend.max_values(e, extra_constraints=c, result=self.result, solver=self._get_solver())
            self._cache_eval(e, vals, exact=exact, cache=cache)
            return max(vals)
        except BackendError:
            pass

        try:
            return self._solver_backend.max(e, extra_constraints=c, result=self.result, solver=self._get_solver())
        except BackendError:
            e_type, value, traceback = sys.exc_info()
            raise ClaripyFrontendError, "Backend error during _max: %s('%s')" % (str(e_type), str(value)), traceback

    def _min(self, e, extra_constraints=(), exact=None, cache=None):
        if not self.satisfiable(extra_constraints=extra_constraints):
            raise UnsatError("Unsat during _min()")

        l.debug("Frontend.min() with %d extra_constraints", len(extra_constraints))

        two = self.eval(e, 2, extra_constraints=extra_constraints)
        if len(two) == 0: raise UnsatError("unsat during min()")
        elif len(two) == 1: return two[0]

        self.simplify()

        c = extra_constraints + (ULE(e, two[0]), ULE(e, two[1]))
        try:
            vals = self._solver_backend.min_values(e, extra_constraints=c, result=self.result, solver=self._get_solver())
            self._cache_eval(e, vals, exact=exact, cache=cache)
            return min(vals)
        except BackendError:
            pass

        try:
            return self._solver_backend.min(e, extra_constraints=c, result=self.result, solver=self._get_solver())
        except BackendError:
            e_type, value, traceback = sys.exc_info()
            raise ClaripyFrontendError, "Backend error during _min: %s('%s')" % (str(e_type), str(value)), traceback

    def _solution(self, e, v, extra_constraints=(), exact=None, cache=None):
        try:
            b = self._solver_backend.solution(e, v, extra_constraints=extra_constraints, solver=self._get_solver())
        except BackendError:
            e_type, value, traceback = sys.exc_info()
            raise ClaripyFrontendError, "Backend error during _solution: %s('%s')" % (str(e_type), str(value)), traceback

        return b

    def _is_true(self, e, extra_constraints=(), exact=None, cache=None):
        try:
            b = self._solver_backend.is_true(e, extra_constraints=extra_constraints, solver=self._get_solver())
        except BackendError:
            e_type, value, traceback = sys.exc_info()
            raise ClaripyFrontendError, "Backend error during _is_true: %s('%s')" % (str(e_type), str(value)), traceback

        return b

    def _is_false(self, e, extra_constraints=(), exact=None, cache=None):
        try:
            b = self._solver_backend.is_false(e, extra_constraints=extra_constraints, solver=self._get_solver())
        except BackendError:
            e_type, value, traceback = sys.exc_info()
            raise ClaripyFrontendError, "Backend error during _is_false: %s('%s')" % (str(e_type), str(value)), traceback

        return b

    #
    # Serialization and such.
    #

    def downsize(self):
        ConstrainedFrontend.downsize(self)
        self._tls.solver = None
        self._to_add = [ ]

    #
    # Merging and splitting
    #

    def _blank_copy(self):
        return FullFrontend(self._solver_backend, cache=self._cache, timeout=self.timeout)

    def branch(self):
        b = ConstrainedFrontend.branch(self)
        b._tls.solver = getattr(self._tls, 'solver', None) #pylint:disable=no-member
        b._to_add = list(self._to_add)
        return b

    def merge(self, others, merge_flag, merge_values):
        return self._solver_backend.__class__.__name__ == 'BackendZ3', ConstrainedFrontend.merge(self, others, merge_flag, merge_values)[1]

from ..errors import UnsatError, BackendError, ClaripyFrontendError
from ..ast.bv import UGE, ULE
from ..backend_manager import backends
