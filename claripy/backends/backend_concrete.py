import logging
l = logging.getLogger("claripy.backends.backend_concrete")

from .backend import Backend, ops, BackendError
from .. import bv

class BackendConcrete(Backend):
    def __init__(self):
        Backend.__init__(self)
        self._make_raw_ops(set(ops) - { 'BitVec' }, op_module=bv)

    def abstract(self, e):
        if type(e._obj) in (bv.BVV, int, long, str, float):
            return e._obj

        l.debug("%s unable to abstract %s", self.__class__, e._obj.__class__)
        raise BackendError("unable to abstract non-concrete stuff")
