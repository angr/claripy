from .claripy import Claripy
from .solvers import BranchingSolver
from .solvers import CompositeSolver
from .backends import BackendZ3, BackendConcrete, BackendZ3Parallel
from .datalayer import DataLayer

class ClaripyStandalone(Claripy):
    def __init__(self, model_backend=None, solver_backends=None, parallel=False):
        self.parallel = parallel if parallel is not None else False
        b_concrete = BackendConcrete(self)

        if parallel:
            b_z3 = BackendZ3Parallel(self)
        else:
            b_z3 = BackendZ3(self)
        self.z3_backend = b_z3

        solver_backends = [ b_z3 ] if solver_backends is None else solver_backends
        model_backend = b_concrete if model_backend is None else model_backend
        Claripy.__init__(self, model_backend, solver_backends, parallel=parallel)
        self.dl = DataLayer()

    def solver(self):
        return BranchingSolver(self)

    def composite_solver(self):
        return CompositeSolver(self)
