#!/usr/bin/env python

import logging
l = logging.getLogger("claripy.expression")
l.setLevel(logging.DEBUG)

class A(object):
    '''
    An A(ST) tracks a tree of calls (including operations) on arguments.
    '''

    def __init__(self, op, args):
        self._op = op
        self._args = args

    def eval(self, backends, save, model=None):
        args = [ ]
        for a in self._args:
            if isinstance(a, E):
                args.append(a.eval(backends=backends, save=save, model=model))
            elif isinstance(a, A):
                args.append(a.eval(backends, save, model=model))
            else:
                args.append(a)

        for b in backends:
            l.debug("trying evaluation with %s", b)
            try:
                return b.call(self._op, args, model=model)
            except BackendError:
                l.debug("... failed")
                continue

        raise Exception("eval failed with available backends")

    def __repr__(self):
        if '__' in self._op:
            return "%s.%s%s" % (self._args[0], self._op, self._args[1:])
        else:
            return "%s%s" % (self._op, self._args)

class E(object):
    '''
    A base class to wrap Z3 objects.
    '''

    def __init__(self, backends, variables=None, symbolic=None, uuid=None, obj=None, ast=None, stored=False):
        have_uuid = uuid is not None
        have_data = not (variables is None or symbolic is None or (obj is None and ast is None))

        if have_uuid and not have_data:
            e = datalayer.dl.load_expression(uuid)
            self.variables = e.variables
            self.symbolic = e.symbolic

            self._uuid = e._uuid
            self._obj = e._obj
            self._ast = e._ast
            self._backends = e._backends
            self._stored = e._stored
        elif have_data:
            self.variables = variables
            self.symbolic = symbolic

            self._uuid = uuid
            self._obj = obj
            self._ast = ast
            self._backends = backends
            self._stored = stored
        else:
            raise ValueError("invalid arguments passed to E()")

    @property
    def is_abstract(self):
        return self._obj is None

    @property
    def is_actual(self):
        return self._obj is not None

    def __repr__(self):
        if self._obj is not None:
            return "E(%s)" % self._obj
        elif self._ast is not None:
            return "E(%s)" % self._ast
        elif self._uuid is not None:
            return "E(uuid=%s)" % self._uuid

    def _do_op(self, op_name, args):
        for b in self._backends:
            try:
                return b.call(op_name, (self,)+args)
            except BackendError:
                continue

        raise Exception("no backend can handle operation %s", op_name)

    def eval(self, backends=None, save=True, model=None):
        if self._obj is not None:
            l.debug("eval() called with an existing obj")
            return self._obj

        if isinstance(self._ast, A):
            r = self._ast.eval(backends if backends is not None else self._backends, save=save, model=model)
            if save:
                if isinstance(r, E):
                    self._obj = r._obj
                    self.variables = r.variables
                    self.symbolic = r.symbolic
                else:
                    self._obj = r
                return self
            else:
                return r
        else:
            r = self._ast
            if save:
                self._obj = r
                return self
            return r

    def abstract(self, backends=None):
        if self._ast is not None:
            l.debug("abstract() called with an existing ast")
            return

        for b in backends if backends is not None else self._backends:
            l.debug("trying abstraction with %s", b)
            try:
                r = b.abstract(self)
                if isinstance(r, E):
                    self._ast = r._ast
                    self.variables = r.variables
                    self.symbolic = r.symbolic
                else:
                    self._ast = r

                l.debug("... success!")
                return
            except BackendError:
                l.debug("... BackendError!")
                continue

        raise Exception("abstraction failed with available backends")

    #
    # Storing and loading of expressions
    #

    def store(self):
        datalayer.dl.store_expression(self)

    def __getstate__(self):
        if self._uuid is not None:
            l.debug("uuid pickle on %s", self)
            return self._uuid
        l.debug("full pickle on %s", self)

        if self._ast is None:
            self.abstract()
        return self._uuid, self._ast, self.variables, self.symbolic

    def __setstate__(self, s):
        if type(s) is str:
            self.__init__([ ], uuid=s)
            return

        uuid, ast, variables, symbolic = s
        self.__init__([ ], variables=variables, symbolic=symbolic, ast=ast, uuid=uuid)

#
# Wrap stuff
#
operations = {
    # arithmetic
    '__add__', '__radd__',
    '__div__', '__rdiv__',
    '__truediv__', '__rtruediv__',
    '__floordiv__', '__rfloordiv__',
    '__mul__', '__rmul__',
    '__sub__', '__rsub__',
    '__pow__', '__rpow__',
    '__mod__', '__rmod__',
    '__divmod__', '__rdivmod__',

    # comparisons
    '__eq__',
    '__ne__',
    '__ge__', '__le__',
    '__gt__', '__lt__',

    # bitwise
    '__neg__',
    '__pos__',
    '__abs__',
    '__invert__',
    '__or__', '__ror__',
    '__and__', '__rand__',
    '__xor__', '__rxor__',
    '__lshift__', '__rlshift__',
    '__rshift__', '__rrshift__',
}

opposites = {
    '__add__': '__radd__', '__radd__': '__add__',
    '__div__': '__rdiv__', '__rdiv__': '__div__',
    '__truediv__': '__rtruediv__', '__rtruediv__': '__truediv__',
    '__floordiv__': '__rfloordiv__', '__rfloordiv__': '__floordiv__',
    '__mul__': '__rmul__', '__rmul__': '__mul__',
    '__sub__': '__rsub__', '__rsub__': '__sub__',
    '__pow__': '__rpow__', '__rpow__': '__pow__',
    '__mod__': '__rmod__', '__rmod__': '__mod__',
    '__divmod__': '__rdivmod__', '__rdivmod__': '__divmod__',

    '__eq__': '__eq__',
    '__ne__': '__ne__',
    '__ge__': '__le__', '__le__': '__ge__',
    '__gt__': '__lt__', '__lt__': '__gt__',

    #'__neg__':
    #'__pos__':
    #'__abs__':
    #'__invert__':
    '__or__': '__ror__', '__ror__': '__or__',
    '__and__': '__rand__', '__rand__': '__and__',
    '__xor__': '__rxor__', '__rxor__': '__xor__',
    '__lshift__': '__rlshift__', '__rlshift__': '__lshift__',
    '__rshift__': '__rrshift__', '__rrshift__': '__rshift__',
}

def wrap_operator(cls, op_name):
    def wrapper(self, *args):
        return self._do_op(op_name, args)
    wrapper.__name__ = op_name

    setattr(cls, op_name, wrapper)

def make_methods(cls):
    for name in operations:
        wrap_operator(cls, name)
make_methods(E)

from .backends.backend import BackendError
from . import datalayer
