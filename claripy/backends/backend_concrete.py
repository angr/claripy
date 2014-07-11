import logging
l = logging.getLogger("claripy.backends.backend_concrete")

from .backend import Backend, ops, BackendError
from .. import bv

class BackendConcrete(Backend):
    def __init__(self):
        Backend.__init__(self)
        self._make_raw_ops(set(ops) - { 'BitVec' }, op_module=bv)
        self._op_raw['BitVec'] = self.BitVec

    def BitVec(self, name, size, model=None): #pylint:disable=W0613,R0201
        if model is None:
            l.debug("BackendConcrete can only handle BitVec when we are given a model")
            raise BackendError("BackendConcrete can only handle BitVec when we are given a model")
        else:
            return model[name]

    def process_args(self, args, exprs, model=None):
        processed = [ ]
        for a,e in zip(args, exprs):
            if isinstance(e, E) and e.symbolic:
                l.debug("BackendConcrete.process_args() aborting on symbolic expression")
                raise BackendError("BackendConcrete.process_args() aborting on symbolic expression")

            if type(a) is None:
                l.debug("BackendConcrete doesn't handle abstract stuff")
                raise BackendError("BackendConcrete doesn't handle abstract stuff")

            if hasattr(a, '__module__') and a.__module__ == 'z3':
                if hasattr(a, 'as_long'):
                    processed.append(bv.BVV(a.as_long(), a.size()))
                else:
                    l.warning("TODO: support more complex non-symbolic expressions, maybe?")
                    raise BackendError("TODO: support more complex non-symbolic expressions, maybe?")
            else:
                processed.append(a)

        return processed

    def abstract(self, e):
        if type(e._obj) in (bv.BVV, int, long, str, float):
            return e._obj

        l.debug("%s unable to abstract %s", self.__class__, e._obj.__class__)
        raise BackendError("unable to abstract non-concrete stuff")

from ..expression import E
