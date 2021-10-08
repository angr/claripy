import logging
from ..ast.bv import BV
from ..ast.base import Base
from ..errors import ClaripyOperationError
from .. import operations

l = logging.getLogger("claripy.ast.func")

class Func(Base):

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.func_name = self.args[0]
        self.func_args = self.args
        args_type = [type(arg) for arg in self.func_args]
        self.func_op = operations.op(self.func_name, args_type, BV, bound=False, calc_length=lambda *a: 64)
        #operations.backend_func_operations.add(self.op)

    def func_name(self):
        return self.func_name


FUNC = operations.op('FUNC', BV, BV, bound=False)