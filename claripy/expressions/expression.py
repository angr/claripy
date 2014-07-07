#!/usr/bin/env python

# pylint: disable=F0401

import logging
l = logging.getLogger("claripy.expressions.expression")

class Expression(object):
	'''
	A base class to wrap Z3 objects.
	'''

	def __init__(self, variables, symbolic, uuid):
		self._uuid = uuid
		self.variables = variables
		self.symbolic = symbolic

	def _do_op(self, op_name, args):
		raise NotImplementedError("_do_op must be overloaded.")

	@staticmethod
	def _op_args(backend, op_name, args, obj=None):
		'''
		Returns the function object (representing the operation) and the
		arguments to pass to that function object.
		'''

		if '__' in op_name:
			if obj is None:
				op = getattr(args[0], op_name)
				op_args = args[1:]
			else:
				op = getattr(obj, op_name)
				op_args = args
		else:
			if obj is None:
				op = backend.op(op_name)
				op_args = args
			else:
				op = backend.op(op_name)
				op_args = [ obj ] + args

		return op, op_args


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
