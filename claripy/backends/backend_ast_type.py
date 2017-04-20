from . import Backend
class BackendASTType(Backend):
    def __init__(self):
        Backend.__init__(self)

        for o in operations.resulting_boolean_operations:
            self._op_expr[o] = lambda a: Bool
        for o in operations.resulting_bv_operations:
            self._op_expr[o] = lambda a: BV
        for o in operations.resulting_fp_operations:
            self._op_expr[o] = lambda a: FP

from ..ast.bv import BV
from ..ast.fp import FP
from ..ast.bool import Bool
from .. import operations
