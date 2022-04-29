import logging
from ..ast.bv import BV
from ..ast.base import Base
from ..errors import ClaripyOperationError
from .. import operations

l = logging.getLogger("claripy.ast.func")

class Func(Base):

    def __init__(self, *args, **kwargs):
        #super().__init__(*args, **kwargs)
        self.ret_size = self._ret_size if self._ret_size is not None else 32

        self.func_name = self.op
        self.args = self.args
        args_type = [type(arg) for arg in self.args]
        self.func_op = operations.op(self.func_name, args_type, BV, bound=False, calc_length=lambda *a: self.ret_size)
        #operations.backend_func_operations.add(self.op)

    def get_func_name(self):
        return self.func_name


#FUNC = operations.op('FUNC', BV, BV, bound=False)

class MemoryLoad(Base):
    def __init__(self,  *args, **kwargs):
        self.ret_size = self._ret_size if self._ret_size is not None else 32
        self.args = self.args
        self.op = operations.op('MemoryLoad', BV, BV, bound=False, calc_length=lambda *a: self.ret_size)
