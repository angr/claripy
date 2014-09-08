#import operator

import logging
l = logging.getLogger('claripy.backends.backend')

class BackendError(Exception):
	pass

class Backend(object):
	def __init__(self, claripy):
		self._claripy = claripy
		self._op_raw = { }
		self._op_expr = { }

	def _make_raw_ops(self, op_list, op_dict=None, op_module=None):
		for o in op_list:
			self._op_raw[o] = op_dict[o] if op_dict is not None else getattr(op_module, o)

	#
	# These functions handle converting expressions to formats that the backend
	# can understand.
	#

	def convert(self, r, result=None): #pylint:disable=W0613,R0201
		'''
		Converts r to something usable by this backend.
		'''
		return r

	def convert_expr(self, expr, save=None, result=None): #pylint:disable=R0201
		'''
		Resolves a claripy.E into something usable by the backend.
		'''
		save = save if save is not None else result is None

		if not isinstance(expr, E):
			return self.convert(expr, result=result)

		if self in expr.objects:
			r = expr.objects[self]
		elif type(expr._ast) is not A:
			r = self.convert(expr._ast, result=result)
		else:
			resolved = False

			for o in expr.objects:
				try:
					 r = self.convert(o, result=result)
					 resolved = True
				except BackendError:
					pass

			if not resolved:
				r = self.call_expr(expr._ast._op, expr._ast._args, result=result)

		if save:
			expr.objects[self] = r
		return r

	def convert_exprs(self, args, result=None):
		return [ self.convert_expr(a, result=result) for a in args ]

	#
	# These functions provide support for applying operations to expressions.
	#

	def call_expr(self, name, args, result=None):
		'''
		Calls operation 'name' on expressions 'args'.

		@returns an Expression with the result.
		'''

		l.debug("%s.call(name=%s, args=%s)", self.__class__.__name__, name, args)

		if name in self._op_expr:
			return self._op_expr[name](*args, result=result)
		else:
			return self.call(name, self.convert_exprs(args), result=result)

	def call(self, name, args, result=None): #pylint:disable=unused-argument
		l.debug("args = %r", args)

		if name in self._op_raw:
			# the raw ops don't get the model, cause, for example, Z3 stuff can't take it
			obj = self._op_raw[name](*args)
		elif not name.startswith("__"):
			l.debug("backend has no operation %s", name)
			raise BackendError("backend has no operation %s" % name)
		else:
			obj = NotImplemented

			# first, try the operation with the first guy
			if hasattr(args[0], name):
				op = getattr(args[0], name)
				obj = op(*args[1:])
			# now try the reverse operation with the second guy
			if obj is NotImplemented and len(args) == 2 and hasattr(args[1], opposites[name]):
				op = getattr(args[1], opposites[name])
				obj = op(args[0])

			if obj is NotImplemented:
				l.debug("%s neither %s nor %s apply on %s", self, name, opposites[name], args)
				raise BackendError("unable to apply operation on provided args")

		l.debug("Returning object %s", obj)
		return obj

	#
	# Abstraction and resolution.
	#

	def abstract(self, e, split_on=None): #pylint:disable=W0613,R0201
		raise BackendError("backend %s doesn't implement abstract()" % self.__class__.__name__)

	#
	# These functions simplify expressions.
	#

	def simplify_expr(self, e):
		o = self.simplify(self.convert_expr(e))
		return E(self._claripy, ast=self.abstract(o), objects={self: o}, variables=e.variables, symbolic=e.symbolic, length=e.length) # TODO: keep UUID

	def simplify(self, e): # pylint:disable=R0201
		return e

from ..expression import E, A
from ..operations import opposites
