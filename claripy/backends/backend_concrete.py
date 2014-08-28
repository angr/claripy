import logging
l = logging.getLogger("claripy.backends.backend_concrete")

from .backend import Backend, ops, BackendError
from .. import bv
import z3
zTrue = z3.BoolVal(True)
zFalse = z3.BoolVal(False)

class BackendConcrete(Backend):
    def __init__(self, claripy):
        Backend.__init__(self, claripy)
        self._make_raw_ops(set(ops) - { 'BitVec' }, op_module=bv)
        self._op_raw['size'] = self.size
        self._op_expr['BitVec'] = self.BitVec

    def BitVec(self, name, size, model=None): #pylint:disable=W0613,R0201
        if model is None:
            l.debug("BackendConcrete can only handle BitVec when we are given a model")
            raise BackendError("BackendConcrete can only handle BitVec when we are given a model")
        else:
            return model[name]

    def size(self, e):
        return e.size()

    def convert(self, a, model=None):
        if type(a) is None:
            l.debug("BackendConcrete doesn't handle abstract stuff")
            raise BackendError("BackendConcrete doesn't handle abstract stuff")

        if type(a) in { int, long, float, bool, str, BVV }:
            return a
        elif hasattr(a, 'as_long'):
            return bv.BVV(a.as_long(), a.size())
        elif isinstance(a, z3.BoolRef):
            try:
                while not z3_lock.acquire(blocking=False):
                    print "BOOL LOCK ACQUISITION FAILED"
                    __import__('time').sleep(1)
                if a.eq(zTrue): return True
                elif a.eq(zFalse): return False
                else:
                    raise BackendError("TODO: support a wider range of non-symbolic Bool expressions")
            finally:
                z3_lock.release()
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

    def convert_expr(self, e, model=None):
        if isinstance(e, E):
            if e.symbolic and model is None:
                l.debug("BackendConcrete.convert_exprs() aborting on symbolic expression")
                raise BackendError("BackendConcrete.convert_exprs() aborting on symbolic expression")

            a = e.eval()
        else:
            a = e
        return self.convert(a)

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

from ..expression import E
from ..bv import BVV
from .backend_z3 import z3_lock
