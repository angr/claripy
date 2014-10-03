#!/usr/bin/env python

import collections
import logging
l = logging.getLogger("claripy.expression")

from .storable import Storable

class A(object):
    '''
    An A(ST) tracks a tree of operations on arguments.
    '''

    __slots__ = [ '_op', '_args', '_hash', '__weakref__' ]

    def __init__(self, op, args):
        self._op = op
        self._args = args
        self._hash = None

    def resolve(self, b, save=None, result=None):
        if result is not None and self in result.resolve_cache[b]:
            return result.resolve_cache[b][self]

        args = [ ]
        for a in self._args:
            if isinstance(a, E):
                args.append(b.convert_expr(a, result=result))
            elif isinstance(a, A):
                args.append(a.resolve(b, save=save, result=result))
            else:
                args.append(b.convert(a, result=result))

        l.debug("trying evaluation with %s", b)
        r = b.call(self._op, args, result=result)
        if result is not None:
            result.resolve_cache[b][self] = r
        return r

    def __repr__(self):
        if '__' in self._op:
            return "%s.%s%s" % (self._args[0], self._op, self._args[1:])
        else:
            return "%s%s" % (self._op, self._args)

    def __hash__(self):
        if self._hash is None:
            self._hash = hash((self._op,) + tuple(self._args))
        return self._hash

    def __getstate__(self):
        return self._op, self._args
    def __setstate__(self, state):
        self._hash = None
        self._op, self._args = state

class E(Storable):
    '''
    A class to wrap expressions.
    '''
    __slots__ = [ 'length', 'variables', 'symbolic', '_uuid', '_model', '_stored', 'objects', '_simplified', '__weakref__' ]

    def __init__(self, claripy, length=None, variables=None, symbolic=None, uuid=None, objects=None, model=None, stored=False, simplified=False):
        Storable.__init__(self, claripy, uuid=uuid)
        have_uuid = uuid is not None
        have_data = not (variables is None or symbolic is None or model is None or length is None)
        self.objects = { }
        self._simplified = simplified

        if have_uuid and not have_data:
            self._load()
        elif have_data:
            self.variables = variables
            self.symbolic = symbolic
            self.length = length

            self._uuid = uuid
            self._model = model
            self._stored = stored

            if objects is not None:
                self.objects.update(objects)
        else:
            raise ValueError("invalid arguments passed to E()")

    #
    # Some debug stuff:
    #

    @staticmethod
    def _part_count(a):
        return sum([ E._part_count(aa) for aa in a._args ]) if isinstance(a, A) else E._part_count(a._model) if isinstance(a, E) else 1

    @staticmethod
    def _depth(a):
        return max([ E._depth(aa)+1 for aa in a._args ]) if isinstance(a, A) else E._depth(a._model) if isinstance(a, E) else 1

    @staticmethod
    def _hash_counts(a, d=None):
        if d is None: d = collections.defaultdict(int)
        d[(a.__class__, hash(a))] += 1

        if isinstance(a, A):
            for aa in a._args:
                E._hash_counts(aa, d=d)
        elif isinstance(a, E):
            E._hash_counts(a._model, d=d)
        return d

    def __hash__(self):
        return hash(self._model)

    def _load(self):
        e = self._claripy.datalayer.load_expression(self._uuid)
        self.variables = e.variables
        self.symbolic = e.symbolic

        self._uuid = e._uuid
        self._model = e._model
        self._stored = e._stored

    def __nonzero__(self):
        raise ClaripyExpressionError('testing Expressions for truthiness does not do what you want, as these expressions can be symbolic')

    def __repr__(self):
        name = "E"
        if self.symbolic:
            name += "S"
        return name + "(%s)" % self._model

    def split(self, split_on):
        if not isinstance(self._model, A):
            return [ self ]

        if self._model._op in split_on:
            l.debug("Trying to split: %r", self._model)
            if all(isinstance(a, E) for a in self._model._args):
                return self._model._args[:]
            else:
                raise ClaripyExpressionError('the abstraction of this expression was not done with "%s" in split_on' % self._model._op)
        else:
            l.debug("no split for you")
            return [ self ]

    #
    # Storing and loading of expressions
    #

    def store(self):
        self._claripy.datalayer.store_expression(self)

    def __getstate__(self):
        if self._uuid is not None:
            l.debug("uuid pickle on %s", self)
            return self._uuid
        l.debug("full pickle on %s", self)
        return self._uuid, self._model, self.variables, self.symbolic, self.length, self._simplified

    def __setstate__(self, s):
        if type(s) is str:
            self.__init__(get_claripy(), uuid=s)
            return

        uuid, model, variables, symbolic, length, simplified = s
        self.__init__(get_claripy(), variables=variables, symbolic=symbolic, model=model, uuid=uuid, length=length, simplified=simplified)

    #
    # BV operations
    #

    def __len__(self):
        if self.length == -1:
            raise ClaripyExpressionError('this expression has no length')
        return self.length
    size = __len__

    def __iter__(self):
        raise ClaripyExpressionError("Please don't iterate over Expressions!")

    def chop(self, bits=1):
        s = len(self)
        if s % bits != 0:
            raise ValueError("expression length (%d) should be a multiple of 'bits' (%d)" % (len(self), bits))
        elif s == bits:
            return [ self ]
        else:
            return list(reversed([ self[(n+1)*bits - 1:n*bits] for n in range(0, s / bits) ]))

    def reversed(self):
        '''
        Reverses the expression.
        '''
        return self._claripy.Reverse(self)
    reverse = reversed

    def __getitem__(self, rng):
        if type(rng) is slice:
            return self._claripy.Extract(int(rng.start), int(rng.stop), self)
        else:
            return self._claripy.Extract(int(rng), int(rng), self)

    def zero_extend(self, n):
        return self._claripy.ZeroExt(n, self)

    def sign_extend(self, n):
        return self._claripy.SignExt(n, self)

#
# Wrap stuff
#

def e_operator(cls, op_name):
    def wrapper(self, *args):
        return self._claripy._do_op(op_name, (self,) + tuple(args))
    wrapper.__name__ = op_name
    setattr(cls, op_name, wrapper)

def make_methods():
    for name in expression_operations:
        e_operator(E, name)

from .errors import ClaripyExpressionError
from .operations import expression_operations
make_methods()
from . import get_claripy
