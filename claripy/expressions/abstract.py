#!/usr/bin/env python

import logging
l = logging.getLogger("claripy.expression.abstract")

from .expression import Expression

class AbstractExpression(Expression):
	def __init__(self, uuid=None, op=None, args=None, variables=None, symbolic=None):
		Expression.__init__(self, variables, symbolic, uuid)
		if op is not None and args is not None:
			self._op = op
			self._args = args

		if uuid is None and op is None and args is None:
			raise TypeError("Incorrect arguments passed to AbstratExpression()")

	def __str__(self):
		if hasattr(self, 'uuid'):
			return "%s(uuid=%s)" % (self.__class__.__name__, self._uuid)
		elif '__' in self._op:
			return "%s.%s%s" % (self._args[0], self._op, self._args[1:])
		else:
			return "%s%s" % (self._op, self._args)

	def __repr__(self):
		return self.__str__()

	def _do_op(self, op_name, right_args):
		l.debug("%s called.", op_name)

		args = (self,) + right_args
		variables = set()
		symbolic = False

		for a in args:
			if isinstance(a, Expression):
				variables |= a.variables
				symbolic |= a.symbolic

		return AbstractExpression(op=op_name, args=args, symbolic=symbolic, variables=variables)

	def actualize(self, backend):
		args = [ ]
		for a in self._args:
			if isinstance(a, Expression):
				args.append(a.actualize(backend)._obj)
			else:
				args.append(a)
		op, args = self._op_args(backend, self._op, args)
		c = op(*args)

		if isinstance(c, Expression):
			raise Exception("WTF")
		elif type(c) in ( long, int, float, str ):
			obj = c
			variables = set()
			symbolic = False
		else:
			obj = c
			variables = self.variables
			symbolic = self.symbolic

		return ActualExpression(backend, obj, variables, symbolic, uuid=self._uuid)

from .actual import ActualExpression
