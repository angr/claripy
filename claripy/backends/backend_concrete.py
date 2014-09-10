import logging
l = logging.getLogger("claripy.backends.backend_concrete")

import z3
zTrue = z3.BoolVal(True)
zFalse = z3.BoolVal(False)

from .backend import Backend, BackendError

class BackendConcrete(Backend):
    def __init__(self, claripy):
        Backend.__init__(self, claripy)
        self._make_raw_ops(set(backend_operations) - { 'BitVec' }, op_module=bv)
        self._op_raw['size'] = self.size
        self._op_raw_result['BitVec'] = self.BitVec

    def BitVec(self, name, size, result=None): #pylint:disable=W0613,R0201
        if result is None:
            l.debug("BackendConcrete can only handle BitVec when we are given a model")
            raise BackendError("BackendConcrete can only handle BitVec when we are given a model")
        if name not in result.model:
            l.debug("BackendConcrete needs variable %s in the model", name)
            raise BackendError("BackendConcrete needs variable %s in the model" % name)
        else:
            return result.model[name]

    @staticmethod
    def size(e):
        if type(e) in { BVV }:
            return e.size()
        else:
            raise BackendError("can't get size of type %s" % type(e))

    def convert(self, a, result=None):
        if type(a) in { int, long, float, bool, str, BVV }:
            return a

        if hasattr(a, 'as_long'): return bv.BVV(a.as_long(), a.size())
        elif isinstance(a, z3.BoolRef) and a.eq(zTrue): return True
        elif isinstance(a, z3.BoolRef) and a.eq(zFalse): return False
        elif result is not None and a.num_args() == 0:
            name = a.decl().name()
            if name in result.model:
                return result.model[name]
            else:
                l.debug("returning 0 for %s (not in model %r)", name, result.model)
                return bv.BVV(0, a.size())
        else:
            l.warning("TODO: support more complex non-symbolic expressions, maybe?")
            raise BackendError("TODO: support more complex non-symbolic expressions, maybe?")

from ..bv import BVV
from ..operations import backend_operations
from .. import bv
