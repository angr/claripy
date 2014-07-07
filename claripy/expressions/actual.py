#!/usr/bin/env python

# pylint: disable=F0401

import logging
l = logging.getLogger("claripy.expression.actual")

from .expression import Expression

class ActualExpression(Expression):
    '''
    A class to wrap Z3 objects so that we can serialize them.
    '''

    def __init__(self, backend, obj, variables, symbolic, uuid=None):
        self._backend = backend

        self._obj = obj
        Expression.__init__(self, variables, symbolic, uuid)

    def __repr__(self):
        return "%s(%s)" % (self.__class__.__name__, self._obj)

    def _do_op(self, op_name, args):
        raw_args = [ ]
        variables = set()
        symbolic = [ ]

        for a in args:
            if type(a) == ActualExpression:
                variables |= a.variables
                symbolic.append(a.symbolic)
                raw_args.append(a._obj)
            else:
                raw_args.append(a)

        op, op_args = self._op_args(self._backend, op_name, raw_args, obj=self._obj)
        return ActualExpression(self._backend, op(*op_args), variables=variables, symbolic=any(symbolic))

    def abstract(self):
        return self._backend.abstract(self._obj)
