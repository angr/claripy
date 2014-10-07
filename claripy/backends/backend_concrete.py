import logging
l = logging.getLogger("claripy.backends.backend_concrete")

import z3
zTrue = z3.BoolVal(True)
zFalse = z3.BoolVal(False)

from .backend import BackendError
from .model_backend import ModelBackend

class BackendConcrete(ModelBackend):
    def __init__(self):
        ModelBackend.__init__(self)
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
        if type(e) is bool:
            return None
        if type(e) in { BVV }:
            return e.size()
        else:
            raise BackendError("can't get size of type %s" % type(e))

    def convert(self, a, result=None):
        if type(a) in { int, long, float, bool, str, BVV }:
            return a

        if not hasattr(a, '__module__') or a.__module__ != 'z3':
            raise BackendError("BackendConcrete got an unsupported type %s", a.__class__)

        z3_backend = self._claripy.backend_of_type(BackendZ3)
        if z3_backend is None:
            raise BackendError("can't convert z3 expressions when z3 is not in use")

        try:
            if hasattr(z3_backend, '_lock'):
                z3_backend._lock.acquire()

            if hasattr(a, 'as_long'): return bv.BVV(a.as_long(), a.size())
            elif isinstance(a, z3.BoolRef) and a.eq(zTrue): return True
            elif isinstance(a, z3.BoolRef) and a.eq(zFalse): return False
            elif result is not None and a.num_args() == 0:
                name = a.decl().name()
                if name in result.model:
                    return result.model[name]
                else:
                    l.debug("returning 0 for %s (not in model)", name)
                    return bv.BVV(0, a.size())
            else:
                #import ipdb; ipdb.set_trace()
                #l.warning("TODO: support more complex non-symbolic expressions, maybe?")
                raise BackendError("TODO: support more complex non-symbolic expressions, maybe?")
        finally:
            if hasattr(z3_backend, '_lock'):
                z3_backend._lock.release()

    #
    # Evaluation functions
    #

    def eval(self, expr, n, result=None):
        return [ self.convert_expr(expr, result=result if n == 1 else None) ]
    def max(self, expr, result=None):
        return self.convert_expr(expr, result=result)
    def min(self, expr, result=None):
        return self.convert_expr(expr, result=result)
    def solution(self, expr, v, result=None):
        return self.convert_expr(expr, result=result) == v

from ..bv import BVV
from ..operations import backend_operations
from .. import bv
from .backend_z3 import BackendZ3
