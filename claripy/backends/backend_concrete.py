import logging
l = logging.getLogger("claripy.backends.backend_concrete")

from .backend import Backend, ops, BackendError
from .. import bv

class BackendConcrete(Backend):
    def __init__(self, claripy):
        Backend.__init__(self, claripy)
        self._make_raw_ops(set(ops) - { 'BitVec' }, op_module=bv)
        self._op_expr['BitVec'] = self.BitVec

    def BitVec(self, name, size, model=None): #pylint:disable=W0613,R0201
        if model is None:
            l.debug("BackendConcrete can only handle BitVec when we are given a model")
            raise BackendError("BackendConcrete can only handle BitVec when we are given a model")
        else:
            return model[name]

    def convert(self, a, model=None):
        if type(a) is None:
            l.debug("BackendConcrete doesn't handle abstract stuff")
            raise BackendError("BackendConcrete doesn't handle abstract stuff")

        if hasattr(a, '__module__') and a.__module__ == 'z3':
            if hasattr(a, 'as_long'):
                return bv.BVV(a.as_long(), a.size())
            elif model is not None and a.num_args() == 0:
                name = a.decl().name()
                if name in model:
                    return bv.BVV(model[name], a.size())
                else:
                    l.debug("returning 0 for %s (not in model %r)", name, model)
                    return bv.BVV(0, a.size())
            else:
                l.warning("TODO: support more complex non-symbolic expressions, maybe?")
                raise BackendError("TODO: support more complex non-symbolic expressions, maybe?")
        else:
            return a

    def convert_expr(self, e, model=None):
        if isinstance(e, E):
            if e.symbolic:
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

from ..expression import E
#from .backend_z3 import BackendZ3
