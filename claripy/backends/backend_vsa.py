import logging
l = logging.getLogger("claripy.backends.backend_vsa")

from .backend import Backend, BackendError

class BackendVSA(Backend):
    def __init__(self):
        Backend.__init__(self)
        self._make_raw_ops(set(expression_operations), op_module=StridedInterval)
        self._make_raw_ops(set(backend_operations_vsa_compliant), op_module=BackendVSA)

    def solver(self, timeout=None):
        s = SolverVSA()
        return s

    def add_exprs(self, solver, constraints):
        pass

    def results_exprs(self, solver, extra_constraints, generic_backend):
        return Result(True, self)

    def convert(self, a, result=None):
        if type(a) in { int, long, float, bool, str, BVV }:
            return a
        if type(a) in { StridedInterval }:
            return a

        import ipdb; ipdb.set_trace()
        raise NotImplementedError()

    def eval(self, s, expr, n, extra_constraints=(), result=None):
        assert type(expr) == StridedInterval

        results = []
        lb = expr.lower_bound

        while len(results) < n and lb < expr.upper_bound:
            results.append(lb)
            lb += expr.stride

        return results

    def min(self, s, expr, extra_constraints=(), result=None):
        assert type(expr) == StridedInterval

        if expr.is_top():
            # TODO: Return
            return StridedInterval.NEG_INF

        return expr.lower_bound

    def max(self, s, expr, extra_constraints=(), result=None):
        assert type(expr) == StridedInterval

        if expr.is_top():
            # TODO:
            return StridedInterval.INF

        return expr.upper_bound

    #
    # Operations
    #
    @staticmethod
    def ULE(expr_1, expr_2):
        pass

    @staticmethod
    def UGE(expr_1, expr_2):
        pass

class SolverVSA():
    def __init__(self):
        pass

from ..bv import BVV
from ..operations import backend_operations_vsa_compliant, expression_operations
from ..vsa import StridedInterval
from ..result import Result