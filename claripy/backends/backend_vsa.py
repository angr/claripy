import logging
l = logging.getLogger("claripy.backends.backend_vsa")

from .model_backend import ModelBackend, BackendError

class BackendVSA(ModelBackend):
    def __init__(self):
        ModelBackend.__init__(self)
        self._make_raw_ops(set(expression_operations), op_module=BackendVSA)
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
        if type(a) in { StridedInterval, ValueSet }:
            return a

        import ipdb; ipdb.set_trace()
        raise NotImplementedError()

    def eval(self, expr, n, result=None):
        assert type(expr) == StridedInterval

        results = []
        lb = expr.lower_bound

        while len(results) < n and lb <= expr.upper_bound:
            results.append(lb)
            lb += expr.stride

        return results

    def min(self, expr, result=None):
        assert type(expr) == StridedInterval

        if expr.is_top():
            # TODO: Return
            return StridedInterval.NEG_INF

        return expr.lower_bound

    def max(self, expr, result=None):
        assert type(expr) == StridedInterval

        if expr.is_top():
            # TODO:
            return StridedInterval.INF

        return expr.upper_bound


    #
    # Operations
    #

    @staticmethod
    def __add__(a, b): return a.__add__(b)

    @staticmethod
    def __sub__(a, b): return a.__sub__(b)

    @staticmethod
    def __and__(a, b): return a.__and__(b)

    # TODO: Implement other operations!

    @staticmethod
    def Concat(*args):
        ret = None
        for expr in args:
            assert type(expr) in { StridedInterval, ValueSet }

            ret = ret.concat(expr) if ret is not None else expr

        return ret

    @staticmethod
    def Extract(*args):
        low_bit = args[1]
        high_bit = args[0]
        expr = args[2]

        assert type(expr) in { StridedInterval, ValueSet }

        ret = expr.extract(high_bit, low_bit)

        return ret


class SolverVSA():
    def __init__(self):
        pass

from ..bv import BVV
from ..operations import backend_operations_vsa_compliant, expression_operations
from ..vsa import StridedInterval, ValueSet
from ..result import Result