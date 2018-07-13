import logging
from multiprocessing import Process, Pool
from functools import partial

from ..utils.transition import raise_from
from .constrained_frontend import ConstrainedFrontend
from ..frontend import Frontend

l = logging.getLogger("claripy.frontends.portfolio_frontend")


def execute_solver_satisfiable(solver, extra_constraints, exact):
    try:
        return solver.satisfiable(
            extra_constraints=extra_constraints,
            exact=exact
        )
    except Exception as e:
        l.debug("Solver %r failed to check satisfiability because %r", solver._solver_backend, e)
        return False


def execute_solver_eval(solver, e, n, extra_constraints, exact):
    try:
        res = solver.eval(
            e, n, extra_constraints=extra_constraints, exact=exact
        )
        print solver._solver_backend
        print res
        return res
    except Exception as e:
        print solver._solver_backend
        print e
        l.debug("Solver %r failed to get solution because %r", solver._solver_backend, e)
        return None


def store_async_result(result, res_list):
    res_list.append(result)


class PortfolioFrontend(Frontend):

    def __init__(self, solvers, *args, **kwargs):
        super(PortfolioFrontend, self).__init__()
        self.solvers = solvers

    # def _blank_copy(self, c):
    #     super(PortfolioFrontend, self)._blank_copy(c)
    #     c.solvers = self.solvers
    #
    # def _copy(self, c):
    #     super(PortfolioFrontend, self)._copy(c)
    #     c.solvers = list(self.solvers)

    def branch(self):
        c = self.blank_copy()
        c.solvers = [solver.branch() for solver in self.solvers]
        return c

    #
    # #
    # # Storable support
    # #
    #
    # def _ana_getstate(self):
    #     return self._solver_backend.__class__.__name__, self.timeout, self._track, ConstrainedFrontend._ana_getstate(self)
    #
    # def _ana_setstate(self, s):
    #     backend_name, self.timeout, self._track, base_state = s
    #     self._solver_backend = backends._backends_by_type[backend_name]
    #     #self._tls = None
    #     self._tls = threading.local()
    #     self._to_add = [ ]
    #     ConstrainedFrontend._ana_setstate(self, base_state)
    #
    @property
    def constraints(self):
        return self.solvers[0].constraints

    def add(self, constraints):
        for solver in self.solvers:
            solver.add(constraints)
        return self.solvers[0]._to_add

    def simplify(self):
        for solver in self.solvers:
            ConstrainedFrontend.simplify(solver)

        # # TODO: should we do this?
        # self._tls.solver = None
        # self._to_add = [ ]

        return self.constraints

    def satisfiable(self, extra_constraints=(), exact=None):
        pool = Pool()
        res_list = []
        # execute in parallel all the solvers, each one in a separate process
        for solver in self.solvers:
            pool.apply_async(
                execute_solver_satisfiable,
                args=(solver, extra_constraints, exact),
                # the call back put the result in the result list
                callback=partial(store_async_result, res_list=res_list)
            )
        # wait until at least one result is True (sat) or until every solver returned False (unsat)
        # The time out is managed internally by every solver
        while True:
            if not any(res_list) or len(res_list) != len(self.solvers):
                break
        # kill the process pool
        # This is useful because as soon as a solver return true we can kill the other solver and speed up the process
        pool.terminate()
        return any(res_list)

    def eval(self, e, n, extra_constraints=(), exact=None):
        if not self.satisfiable(extra_constraints=extra_constraints):
            raise UnsatError('unsat')
        pool = Pool()
        res_list = []
        # execute in parallel all the solvers, each one in a separate process
        for solver in self.solvers:
            pool.apply_async(
                execute_solver_eval,
                args=(solver, e, n, extra_constraints, exact),
                # the call back put the result in the result list
                callback=partial(store_async_result, res_list=res_list)
            )
        # wait until at least one result is meaningful (i.e. not None)
        # The time out is managed internally by every solver
        while True:
            if not any(res_list) or len(res_list) != len(self.solvers):
                break
        # kill the process pool
        # This is useful because as soon as a solver return true we can kill the other solver and speed up the process
        pool.terminate()
        try:
            return [res for res in res_list if res][0]
        except BackendError as e:
            raise_from(ClaripyFrontendError("Backend error during eval"), e)

    #
    # def batch_eval(self, exprs, n, extra_constraints=(), exact=None):
    #     if not self.satisfiable(extra_constraints=extra_constraints):
    #         raise UnsatError('unsat')
    #
    #     try:
    #         return self._solver_backend.batch_eval(
    #             exprs,
    #             n,
    #             extra_constraints=extra_constraints,
    #             solver=self._get_solver(),
    #             model_callback=self._model_hook
    #         )
    #     except BackendError as e:
    #         raise_from(ClaripyFrontendError("Backend error during batch_eval"), e)
    #
    # def max(self, e, extra_constraints=(), exact=None):
    #     if not self.satisfiable(extra_constraints=extra_constraints):
    #         raise UnsatError("Unsat during _max()")
    #
    #     l.debug("Frontend.max() with %d extra_constraints", len(extra_constraints))
    #
    #     two = self.eval(e, 2, extra_constraints=extra_constraints)
    #     if len(two) == 0: raise UnsatError("unsat during max()")
    #     elif len(two) == 1: return two[0]
    #
    #     c = extra_constraints + (UGE(e, two[0]), UGE(e, two[1]))
    #     try:
    #         return self._solver_backend.max(
    #             e, extra_constraints=c,
    #             solver=self._get_solver(),
    #             model_callback=self._model_hook
    #         )
    #     except BackendError as e:
    #         raise_from(ClaripyFrontendError("Backend error during max"), e)
    #
    # def min(self, e, extra_constraints=(), exact=None):
    #     if not self.satisfiable(extra_constraints=extra_constraints):
    #         raise UnsatError("Unsat during _min()")
    #
    #     l.debug("Frontend.min() with %d extra_constraints", len(extra_constraints))
    #
    #     two = self.eval(e, 2, extra_constraints=extra_constraints)
    #     if len(two) == 0: raise UnsatError("unsat during min()")
    #     elif len(two) == 1: return two[0]
    #
    #     c = extra_constraints + (ULE(e, two[0]), ULE(e, two[1]))
    #     try:
    #         return self._solver_backend.min(
    #             e, extra_constraints=c,
    #             solver=self._get_solver(),
    #             model_callback=self._model_hook
    #         )
    #     except BackendError as e:
    #         raise_from(ClaripyFrontendError("Backend error during min"), e)
    #
    # def solution(self, e, v, extra_constraints=(), exact=None):
    #     try:
    #         return self._solver_backend.solution(
    #             e, v, extra_constraints=extra_constraints,
    #             solver=self._get_solver(), model_callback=self._model_hook
    #         )
    #     except BackendError as e:
    #         raise_from(ClaripyFrontendError("Backend error during solution"), e)
    #
    # def is_true(self, e, extra_constraints=(), exact=None):
    #     return e.is_true()
    #     #try:
    #     #   return self._solver_backend.is_true(
    #     #       e, extra_constraints=extra_constraints,
    #     #       solver=self._get_solver(), model_callback=self._model_hook
    #     #   )
    #     #except BackendError:
    #     #   e_type, value, traceback = sys.exc_info()
    #     #   raise ClaripyFrontendError, "Backend error during _is_true: %s('%s')" % (str(e_type), str(value)), traceback
    #
    # def is_false(self, e, extra_constraints=(), exact=None):
    #     return e.is_false()
    #     #try:
    #     #   return self._solver_backend.is_false(
    #     #       e, extra_constraints=extra_constraints,
    #     #       solver=self._get_solver(), model_callback=self._model_hook
    #     #   )
    #     #except BackendError:
    #     #   e_type, value, traceback = sys.exc_info()
    #     #   raise ClaripyFrontendError, "Backend error during _is_false: %s('%s')" % (str(e_type), str(value)), traceback
    #
    # def unsat_core(self, extra_constraints=()):
    #     if self.satisfiable(extra_constraints=extra_constraints):
    #         # all constraints are satisfied
    #         return tuple()
    #
    #     unsat_core = self._solver_backend.unsat_core(self._get_solver())
    #
    #     return tuple(unsat_core)
    #
    # #
    # # Serialization and such.
    # #
    #
    # def downsize(self):
    #     ConstrainedFrontend.downsize(self)
    #     self._tls.solver = None
    #     self._to_add = [ ]
    #
    # #
    # # Merging and splitting
    # #
    #
    # def merge(self, others, merge_conditions, common_ancestor=None):
    #     return self._solver_backend.__class__.__name__ == 'BackendZ3', ConstrainedFrontend.merge(
    #         self, others, merge_conditions, common_ancestor=common_ancestor
    #     )[1]

from ..errors import UnsatError, BackendError, ClaripyFrontendError
from ..ast.bv import UGE, ULE
from ..backend_manager import backends
