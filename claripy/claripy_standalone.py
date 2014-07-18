from .claripy import Claripy
from .solvers import BranchingSolver
from .backends import BackendZ3, BackendConcrete
from .datalayer import DataLayer

class ClaripyStandalone(Claripy):
    def __init__(self):
        expression_backends = [ BackendConcrete(self), BackendZ3(self) ]

        solver_backend = BackendZ3
        results_backend = BackendConcrete
        Claripy.__init__(self, expression_backends, solver_backend, results_backend)
        self.dl = DataLayer()

    def solver(self):
        return BranchingSolver(self)
