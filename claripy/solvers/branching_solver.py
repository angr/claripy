import logging
l = logging.getLogger('claripy.solvers.branching_solver')

from .core_solver import CoreSolver

class BranchingSolver(CoreSolver):
    def __init__(self, claripy, solver_backend=None, results_backend=None, timeout=None, solver=None, result=None):
        CoreSolver.__init__(self, claripy, solver_backend=solver_backend, results_backend=results_backend, timeout=timeout, solver=solver, result=None)
        self._finalized = False

    def add(self, constraints, invalidate_cache=True):
        if self._finalized and invalidate_cache:
            l.debug("%r is finalized...", self)
            self._solver = self._create_solver()
            self._finalized = False
            self._solver.add([e.eval(backends=[self._solver_backend]) for e in self.constraints], invalidate_cache=invalidate_cache)
            l.debug("... de-finalized with %d constriants", len(self.constraints))

        CoreSolver.add(self, constraints, invalidate_cache=invalidate_cache)

    def branch(self):
        s = BranchingSolver(self._claripy, self._solver_backend, self._results_backend, timeout=self._timeout, solver=self._solver, result=self._result)
        s.constraints = self.constraints[:]
        s.variables = set(self.variables)
        s._simplified = self._simplified

        self.finalize()
        s.finalize()

        return s

    def finalize(self):
        self._finalized = True
