from .core_solver import CoreSolver

class BranchingSolver(CoreSolver):
    def __init__(self, claripy, solver_backend=None, results_backend=None, timeout=None):
        CoreSolver.__init__(self, claripy, solver_backend=solver_backend, results_backend=results_backend, timeout=timeout)
        self._finalized = False

    def add(self, *constraints):
        if self._finalized:
            self._create_solver()
            self._finalized = False
            CoreSolver.add(self, self.constraints)

        CoreSolver.add(self, constraints)

    def branch(self):
        s = BranchingSolver(self._claripy, self._solver_backend, self._results_backend, timeout=self._timeout)
        s.constraints = self.constraints[:]
        s._result = self._result
        s.variables = set(self._variables)

        self.finalize()
        s.finalize()

    def finalize(self):
        self._finalized = True
