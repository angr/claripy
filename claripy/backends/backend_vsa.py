import logging
l = logging.getLogger("claripy.backends.backend_vsa")

from .backend import Backend, BackendError

class BackendVSA(Backend):
    def __init__(self):
        Backend.__init__(self)
        self._make_expr_ops(set(expression_operations), op_class=StridedInterval)
        self._make_raw_ops(set(backend_vsa_creation_operations), op_module=BackendVSA)

    def StridedInterval(self, name, size):
        pass

    def convert(self, a, result=None):
        if type(a) in { int, long, float, bool, str, BVV }:
            return a
        if type(a) in { StridedInterval }:
            return a

        raise NotImplementedError()

from ..bv import BVV
from ..operations import backend_operations, backend_vsa_creation_operations, expression_operations
from ..vsa import StridedInterval