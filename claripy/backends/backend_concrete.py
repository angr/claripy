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
        self._op_raw['BitVec'] = self.BitVec

    def BitVec(self, name, size, model=None): #pylint:disable=W0613,R0201
        if model is None:
            l.debug("BackendConcrete can only handle BitVec when we are given a model")
            raise BackendError("BackendConcrete can only handle BitVec when we are given a model")
        else:
            return model[name]

    def size(self, e):
        if type(e) in { BVV }:
            return e.size()
        else:
            raise BackendError("can't get size of type %s" % type(e))

    def convert(self, a, model=None):
        if type(a) in { int, long, float, bool, str, BVV }:
            return a

        try:
            z3_lock.acquire()

            if hasattr(a, 'as_long'): return bv.BVV(a.as_long(), a.size())
            elif isinstance(a, z3.BoolRef) and a.eq(zTrue): return True
            elif isinstance(a, z3.BoolRef) and a.eq(zFalse): return False
            elif model is not None and a.num_args() == 0:
                name = a.decl().name()
                if name in model:
                    return model[name]
                else:
                    l.debug("returning 0 for %s (not in model %r)", name, model)
                    return bv.BVV(0, a.size())
            else:
                l.warning("TODO: support more complex non-symbolic expressions, maybe?")
                raise BackendError("TODO: support more complex non-symbolic expressions, maybe?")
        finally:
            z3_lock.release()

    def abstract(self, e, split_on=None):
        if type(e._obj) in (bv.BVV, int, long, bool, str, float):
            return e._obj

        l.debug("%s unable to abstract %s", self.__class__, e._obj.__class__)
        raise BackendError("unable to abstract non-concrete stuff")

    def primitive(self, o):
        if type(o) in (int, long, bool, str, float):
            return o
        elif type(o) is bv.BVV:
            return o.value
        else:
            raise BackendError("unable to convert type %s to primitive" % o.__class__.__name__)

    def eval(self, s, expr, n, extra_constraints=None, model=None, results_backend=None):
        return [ self.convert(expr, model=model) ]

    def min(self, s, expr, extra_constraints=None, model=None):
        return [ self.convert(expr) ] # no model, since we want to abort on symbolic

    def max(self, s, expr, extra_constraints=None, model=None):
        return [ self.convert(expr) ] # no model, since we want to abort on symbolic

from ..bv import BVV
from .backend_z3 import z3_lock
from ..operations import backend_operations
from .. import bv
