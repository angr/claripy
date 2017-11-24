import logging
import sys
import threading
from ..transition import raise_from

from .constrained_frontend import ConstrainedFrontend

l = logging.getLogger("claripy.frontends.full_frontend")

class FullFrontend(ConstrainedFrontend):
    _model_hook = None

    def __init__(self, solver_backend, timeout=None, track=False, **kwargs):
        ConstrainedFrontend.__init__(self, **kwargs)
        self._track = track
        self._solver_backend = solver_backend
        self.timeout = timeout if timeout is not None else 300000
        self._tls = threading.local()
        self._to_add = [ ]

    def _blank_copy(self, c):
        super(FullFrontend, self)._blank_copy(c)
        c._track = self._track
        c._solver_backend = self._solver_backend
        c.timeout = self.timeout
        c._tls = threading.local()
        c._to_add = [ ]

    def _copy(self, c):
        super(FullFrontend, self)._copy(c)
        c._track = self._track
        c._tls.solver = getattr(self._tls, 'solver', None) #pylint:disable=no-member
        c._to_add = list(self._to_add)

    #
    # Storable support
    #

    def _ana_getstate(self):
        return self._solver_backend.__class__.__name__, self.timeout, self._track, ConstrainedFrontend._ana_getstate(self)

    def _ana_setstate(self, s):
        backend_name, self.timeout, self._track, base_state = s
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
            self._add_constraints()

        if len(self._to_add) > 0:
            self._add_constraints()

        return self._tls.solver

    def _add_constraints(self):
        self._solver_backend.add(self._tls.solver, self.constraints, track=self._track)
        self._to_add = [ ]

    #
    # Constraint management
    #

    def add(self, constraints):
        to_add = ConstrainedFrontend.add(self, constraints)
        self._to_add += to_add
        return to_add

    def simplify(self):
        ConstrainedFrontend.simplify(self)

        # TODO: should we do this?
        self._tls.solver = None
        self._to_add = [ ]

        return self.constraints

    def satisfiable(self, extra_constraints=(), exact=None):
        try:
            return self._solver_backend.satisfiable(
                extra_constraints=extra_constraints,
                solver=self._get_solver(), model_callback=self._model_hook
            )
        except BackendError as e:
            raise_from(ClaripyFrontendError("Backend error during solve"), e)

    def eval(self, e, n, extra_constraints=(), exact=None):
        if not self.satisfiable(extra_constraints=extra_constraints):
            raise UnsatError('unsat')

        try:
            return tuple(self._solver_backend.eval(
                e, n, extra_constraints=extra_constraints,
                solver=self._get_solver(), model_callback=self._model_hook
            ))
        except BackendError as e:
            raise_from(ClaripyFrontendError("Backend error during eval"), e)

    def batch_eval(self, exprs, n, extra_constraints=(), exact=None):
        if not self.satisfiable(extra_constraints=extra_constraints):
            raise UnsatError('unsat')

        try:
            return self._solver_backend.batch_eval(
                exprs,
                n,
                extra_constraints=extra_constraints,
                solver=self._get_solver(),
                model_callback=self._model_hook
            )
        except BackendError as e:
            raise_from(ClaripyFrontendError("Backend error during batch_eval"), e)

    def max(self, e, extra_constraints=(), exact=None):
        if not self.satisfiable(extra_constraints=extra_constraints):
            raise UnsatError("Unsat during _max()")

        l.debug("Frontend.max() with %d extra_constraints", len(extra_constraints))

        two = self.eval(e, 2, extra_constraints=extra_constraints)
        if len(two) == 0: raise UnsatError("unsat during max()")
        elif len(two) == 1: return two[0]

        c = extra_constraints + (UGE(e, two[0]), UGE(e, two[1]))
        try:
            return self._solver_backend.max(
                e, extra_constraints=c,
                solver=self._get_solver(),
                model_callback=self._model_hook
            )
        except BackendError as e:
            raise_from(ClaripyFrontendError("Backend error during max"), e)

    def min(self, e, extra_constraints=(), exact=None):
        if not self.satisfiable(extra_constraints=extra_constraints):
            raise UnsatError("Unsat during _min()")

        l.debug("Frontend.min() with %d extra_constraints", len(extra_constraints))

        two = self.eval(e, 2, extra_constraints=extra_constraints)
        if len(two) == 0: raise UnsatError("unsat during min()")
        elif len(two) == 1: return two[0]

        c = extra_constraints + (ULE(e, two[0]), ULE(e, two[1]))
        try:
            return self._solver_backend.min(
                e, extra_constraints=c,
                solver=self._get_solver(),
                model_callback=self._model_hook
            )
        except BackendError as e:
            raise_from(ClaripyFrontendError("Backend error during min"), e)

    def solution(self, e, v, extra_constraints=(), exact=None):
        try:
            return self._solver_backend.solution(
                e, v, extra_constraints=extra_constraints,
                solver=self._get_solver(), model_callback=self._model_hook
            )
        except BackendError as e:
            raise_from(ClaripyFrontendError("Backend error during solution"), e)

    def is_true(self, e, extra_constraints=(), exact=None):
        return e.is_true()
        #try:
        #   return self._solver_backend.is_true(
        #       e, extra_constraints=extra_constraints,
        #       solver=self._get_solver(), model_callback=self._model_hook
        #   )
        #except BackendError:
        #   e_type, value, traceback = sys.exc_info()
        #   raise ClaripyFrontendError, "Backend error during _is_true: %s('%s')" % (str(e_type), str(value)), traceback

    def is_false(self, e, extra_constraints=(), exact=None):
        return e.is_false()
        #try:
        #   return self._solver_backend.is_false(
        #       e, extra_constraints=extra_constraints,
        #       solver=self._get_solver(), model_callback=self._model_hook
        #   )
        #except BackendError:
        #   e_type, value, traceback = sys.exc_info()
        #   raise ClaripyFrontendError, "Backend error during _is_false: %s('%s')" % (str(e_type), str(value)), traceback

    def unsat_core(self, extra_constraints=()):
        if self.satisfiable(extra_constraints=extra_constraints):
            # all constraints are satisfied
            return tuple()

        unsat_core = self._solver_backend.unsat_core(self._get_solver())

        return tuple(unsat_core)

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

    def merge(self, others, merge_conditions, common_ancestor=None):
        return self._solver_backend.__class__.__name__ == 'BackendZ3', ConstrainedFrontend.merge(
            self, others, merge_conditions, common_ancestor=common_ancestor
        )[1]

from ..errors import UnsatError, BackendError, ClaripyFrontendError
from ..ast.bv import UGE, ULE
from ..backend_manager import backends
