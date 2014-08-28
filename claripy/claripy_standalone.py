from .claripy import Claripy
from .solvers import BranchingSolver
from .solvers import CompositeSolver
from .backends import BackendZ3, BackendConcrete
from .datalayer import DataLayer

class ClaripyStandalone(Claripy):
    def __init__(self, expression_backends=None, solver_backend=None, results_backend=None, parallel=None):
        self.parallel = parallel if parallel is not None else False
        b_concrete = BackendConcrete(self)
        b_z3 = BackendZ3(self)

        expression_backends = [ b_concrete, b_z3 ] if expression_backends is None else expression_backends
        solver_backend = b_z3 if solver_backend is None else solver_backend
        results_backend = b_concrete if results_backend is None else results_backend
        Claripy.__init__(self, expression_backends, solver_backend, results_backend, parallel=parallel)
        self.dl = DataLayer()

    def solver(self):
        return BranchingSolver(self)

    def composite_solver(self):
        return CompositeSolver(self)
