import logging
import threading

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
        super()._blank_copy(c)
        c._track = self._track
        c._solver_backend = self._solver_backend
        c.timeout = self.timeout
        c._tls = threading.local()
        c._to_add = [ ]

    def _copy(self, c):
        super()._copy(c)
        c._track = self._track
        c._tls.solver = getattr(self._tls, 'solver', None) #pylint:disable=no-member
        c._to_add = list(self._to_add)

    #
    # Serialization support
    #

    def __getstate__(self):
        return self._solver_backend.__class__.__name__, self.timeout, self._track, super().__getstate__()

    def __setstate__(self, s):
        backend_name, self.timeout, self._track, base_state = s
        self._solver_backend = backends._backends_by_type[backend_name]
        #self._tls = None
        self._tls = threading.local()
        self._to_add = [ ]
        super().__setstate__(base_state)

    #
    # Frontend Creation
    #

    def _get_solver(self):
        if getattr(self._tls, 'solver', None) is None:
            self._tls.solver = self._solver_backend.solver(timeout=self.timeout)
            self._add_constraints()
        elif self._finalized and len(self._to_add) > 0:
            if not hasattr(self._solver_backend, 'clone_solver') or self._solver_backend.reuse_z3_solver:
                self._tls.solver = self._solver_backend.solver(timeout=self.timeout)
            else:
                self._tls.solver = self._solver_backend.clone_solver(self._tls.solver)
            self._add_constraints()

        if len(self._to_add) > 0:
            self._add_constraints()

        solver = self._tls.solver
        if self._solver_backend.reuse_z3_solver:
            # we must re-add all constraints
            self._add_constraints()
        return solver

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

    def check_satisfiability(self, extra_constraints=(), exact=None):
        try:
            return self._solver_backend.check_satisfiability(
                extra_constraints=extra_constraints,
                solver=self._get_solver(),
                model_callback=self._model_hook
            )
        except BackendError as e:
            raise ClaripyFrontendError("Backend error during solve") from e

    def satisfiable(self, extra_constraints=(), exact=None):
        try:
            return self._solver_backend.satisfiable(
                extra_constraints=extra_constraints,
                solver=self._get_solver(), model_callback=self._model_hook
            )
        except BackendError as e:
            raise ClaripyFrontendError("Backend error during solve") from e

    def eval(self, e, n, extra_constraints=(), exact=None):
        if not self.satisfiable(extra_constraints=extra_constraints):
            raise UnsatError('unsat')

        try:
            return tuple(self._solver_backend.eval(
                e, n, extra_constraints=extra_constraints,
                solver=self._get_solver(), model_callback=self._model_hook
            ))
        except BackendError as exc:
            raise ClaripyFrontendError("Backend error during eval") from exc

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
            raise ClaripyFrontendError("Backend error during batch_eval") from e

    def max(self, e, extra_constraints=(), signed=False, exact=None):
        if not self.satisfiable(extra_constraints=extra_constraints):
            raise UnsatError("Unsat during _max()")

        l.debug("Frontend.max() with %d extra_constraints", len(extra_constraints))

        two = self.eval(e, 2, extra_constraints=extra_constraints)
        if len(two) == 0: raise UnsatError("unsat during max()")
        if len(two) == 1: return two[0]

        if signed:
            c = tuple(extra_constraints) + (SGE(e, two[0]), SGE(e, two[1]))
        else:
            c = tuple(extra_constraints) + (UGE(e, two[0]), UGE(e, two[1]))
        try:
            return self._solver_backend.max(
                e, extra_constraints=c,
                solver=self._get_solver(),
                model_callback=self._model_hook,
                signed=signed,
            )
        except BackendError as exc:
            raise ClaripyFrontendError("Backend error during max") from exc

    def min(self, e, extra_constraints=(), signed=False, exact=None):
        if not self.satisfiable(extra_constraints=extra_constraints):
            raise UnsatError("Unsat during _min()")

        l.debug("Frontend.min() with %d extra_constraints", len(extra_constraints))

        two = self.eval(e, 2, extra_constraints=extra_constraints)
        if len(two) == 0: raise UnsatError("unsat during min()")
        if len(two) == 1: return two[0]

        if signed:
            c = tuple(extra_constraints) + (SLE(e, two[0]), SLE(e, two[1]))
        else:
            c = tuple(extra_constraints) + (ULE(e, two[0]), ULE(e, two[1]))
        try:
            return self._solver_backend.min(
                e, extra_constraints=c,
                solver=self._get_solver(),
                model_callback=self._model_hook,
                signed=signed,
            )
        except BackendError as exc:
            raise ClaripyFrontendError("Backend error during min") from exc

    def solution(self, e, v, extra_constraints=(), exact=None):
        try:
            return self._solver_backend.solution(
                e, v, extra_constraints=extra_constraints,
                solver=self._get_solver(), model_callback=self._model_hook
            )
        except BackendError as exc:
            raise ClaripyFrontendError("Backend error during solution") from exc

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
from ..ast.bv import UGE, ULE, SGE, SLE
from ..backend_manager import backends
