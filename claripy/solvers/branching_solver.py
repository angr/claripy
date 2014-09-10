import logging
l = logging.getLogger('claripy.solvers.branching_solver')

from .solver import Solver

class BranchingSolver(Solver):
    def __init__(self, claripy, timeout=None, solvers=None, to_add=None, result=None):
        Solver.__init__(self, claripy, timeout=timeout, solvers=solvers, to_add=to_add, result=None)
        self._finalized = False

    def add(self, constraints, invalidate_cache=True):
        if self._finalized and invalidate_cache:
            l.debug("%r is finalized...", self)
            self._solver_states = { }
            self._to_add = { }
            self._finalized = False
        Solver.add(self, constraints, invalidate_cache=invalidate_cache)

    def branch(self):
        s = BranchingSolver(self._claripy, timeout=self._timeout, solvers=self._solver_states, to_add=self._to_add, result=self._result)
        s.constraints = self.constraints[:]
        s.variables = set(self.variables)
        s._simplified = self._simplified

        self.finalize()
        s.finalize()
        return s

    def finalize(self):
        self._finalized = True
