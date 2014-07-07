from .backend import Backend, ops
from .. import bv

class BackendConcrete(Backend):
    def __init__(self):
        Backend.__init__(self)
        self._make_ops(set(ops) - { 'BitVec' }, op_module=bv)
