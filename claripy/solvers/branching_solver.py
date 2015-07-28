import logging
l = logging.getLogger('claripy.solvers.branching_solver')

from .solver import Solver

class BranchingSolver(Solver):
    def __init__(self, solver_backend, **solver_kwargs):
        Solver.__init__(self, solver_backend, **solver_kwargs)
        self._finalized = False

    def add(self, constraints, invalidate_cache=True):
        if self._finalized and invalidate_cache:
            l.debug("%r is finalized...", self)
            self._solver = None
            self._to_add = [ ]
            self._finalized = False
        Solver.add(self, constraints, invalidate_cache=invalidate_cache)

    def branch(self):
        s = BranchingSolver(self._solver_backend, timeout=self._timeout, solver=self._solver, to_add=self._to_add, result=self._result)
        s.constraints = self.constraints[:]
        s.variables = set(self.variables)
        s._simplified = self._simplified

        self.finalize()
        s.finalize()
        return s

    def finalize(self):
        self._finalized = True

    def _ana_getstate(self):
        if not self._finalized:
            self.finalize()
        return Solver._ana_getstate(self)

    def _ana_setstate(self, s):
        self._finalized = True
        Solver._ana_setstate(self, s)
