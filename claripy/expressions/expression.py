#!/usr/bin/env python

# pylint: disable=F0401

import logging
l = logging.getLogger("claripy.expressions.expression")

class Expression(object):
	'''
	A base class to wrap Z3 objects.
	'''

	def __init__(self, backends, variables=None, symbolic=None, uuid=None, obj=None):
		if (uuid is None) and (variables is None or symbolic is None and obj is None):
			raise ValueError("invalid arguments passed to Expression()")

		self.variables = variables
		self.symbolic = symbolic

		self._uuid = uuid
		self._obj = obj
		self._backends = backends

	def __repr__(self):
		return "<Expression uuid=%s obj=%s>" % (self._uuid, self._obj)

	def _do_op(self, op_name, args):
		for b in self._backends:
			try:
				return b.call(op_name, (self,)+args)
			except BackendError:
				continue

		raise Exception("no backend can handle operation %s", op_name)

	def actualize(self, new_backends=None):
		if not isinstance(self._obj, AbstractCall):
			raise Exception("actualize() called with a non-abstract obj")

		if new_backends is not None:
			self._backends = new_backends

		for b in self._backends:
			try:
				r = self._obj.apply(b)
				self._obj = r._obj
				self.variables = r.variables
				self.symbolic = r.symbolic
				return
			except BackendError:
				continue

		raise Exception("actualization failed with available backends")

#
# Wrap stuff
#
ops = {
	'__add__', '__and__', '__div__', '__eq__', '__ge__',
	'__gt__', '__invert__', '__le__', '__lshift__', '__lt__',
	'__mod__', '__mul__', '__ne__', '__neg__', '__or__', '__pos__',
	'__radd__', '__rand__', '__rdiv__', '__rlshift__', '__rmod__',
	'__rmul__', '__ror__', '__rrshift__', '__rshift__', '__rsub__',
	'__rtruediv__', '__rxor__', '__sub__', '__truediv__', '__xor__',
}

def wrap_operator(cls, op_name):
	def wrapper(self, *args):
		return self._do_op(op_name, args)
	wrapper.__name__ = op_name

	setattr(cls, op_name, wrapper)

def make_methods(cls):
	for name in ops:
		wrap_operator(cls, name)
make_methods(Expression)

from ..backends.backend import BackendError
from ..backends.abstract_call import AbstractCall
