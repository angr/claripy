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

	def convert(self, r, model=None): #pylint:disable=W0613,R0201
		'''
		Converts r to something usable by this backend.
		'''
		return r

	def primitive(self, o): #pylint:disable=W0613
		'''
		Should return a primitive (int, float, etc) of this value.
		'''

		raise BackendError("Primitive conversion not implemented for %s." % self.__class__.__name__)

	def call(self, name, args, model=None):
		'''
		Calls operation 'name' on expressions 'args'.

		@returns an Expression with the result.
		'''

		l.debug("%s.call(name=%s, args=%s)", self.__class__.__name__, name, args)

		if name in self._op_expr:
			return self._op_expr[name](*args, model=model)

		#variables = reduce(operator.or_, (a.variables for a in args if isinstance(a, E)), set())
		#symbolic = any((a.symbolic for a in args if isinstance(a, E)))
		op_args = self.convert_exprs(args)
		l.debug("op_args = %r", op_args)

		if name in self._op_raw:
			# the raw ops don't get the model, cause, for example, Z3 stuff can't take it
			obj = self._op_raw[name](*op_args)
		elif not name.startswith("__"):
			l.debug("backend has no operation %s", name)
			raise BackendError("backend has no operation %s" % name)
		else:
			obj = NotImplemented

			# first, try the operation with the first guy
			if hasattr(op_args[0], name):
				op = getattr(op_args[0], name)
				obj = op(*op_args[1:])
			# now try the reverse operation with the second guy
			if obj is NotImplemented and len(op_args) == 2 and hasattr(op_args[1], opposites[name]):
				op = getattr(op_args[1], opposites[name])
				obj = op(op_args[0])

			if obj is NotImplemented:
				l.debug("%s neither %s nor %s apply on %s", self, name, opposites[name], op_args)
				raise BackendError("unable to apply operation on provided args")

		#r = self.wrap(obj, variables=variables, symbolic=symbolic)
		#l.debug("Returning expression %s", r)
		l.debug("Returning object %s", obj)
		return obj

	#
	# Abstraction and resolution.
	#

	def abstract(self, e, split_on=None): #pylint:disable=W0613,R0201
		if e._ast is not None:
			return
		else:
			self._abstract(e, split_on=None)

	def _abstract(self, e, split_on=None): #pylint:disable=W0613,R0201
		raise BackendError("backend %s doesn't implement abstract()" % self.__class__.__name__)

	def convert_expr(self, expr, save=None, model=None): #pylint:disable=R0201
		'''
		Resolves a claripy.E into something usable by the backend.
		'''
		save = save if save is not None else model is None

		if not isinstance(expr, E):
			return self.convert(expr, model=model)

		if self in expr.objects:
			r = expr.objects[self]
		elif type(expr._ast) is not A:
			r = self.convert(expr._ast, model=model)
		else:
			resolved = False

			for o in expr.objects:
				try:
					 r = self.convert(o, model=model)
					 resolved = True
				except BackendError:
					pass

			if not resolved:
				r = self.call(expr._ast._op, [ self.convert_expr(e, model=model, save=save) for e in expr._ast._args ], model=model)

		if save:
			expr.objects[self] = r
		return r

	def convert_exprs(self, args, model=None):
		return [ self.convert_expr(a, model=model) for a in args ]


	#
	# Solver support.
	#

	def solver(self): #pylint:disable=W0613,R0201
		raise BackendError("backend doesn't support solving")

	def add(self, s, c): #pylint:disable=W0613,R0201
		raise BackendError("backend doesn't support solving")

	def check(self, s, extra_constraints=None): #pylint:disable=W0613,R0201
		raise BackendError("backend doesn't support solving")

	def results(self, s, extra_constraints=None, generic_model=True): #pylint:disable=W0613,R0201
		raise BackendError("backend doesn't support solving")

	def eval(self, s, expr, n, extra_constraints=None, model=None, results_backend=None): #pylint:disable=W0613,R0201
		raise BackendError("backend doesn't support solving")

	def min(self, s, expr, extra_constraints=None, model=None): #pylint:disable=W0613,R0201
		raise BackendError("backend doesn't support solving")

	def max(self, s, expr, extra_constraints=None, model=None): #pylint:disable=W0613,R0201
		raise BackendError("backend doesn't support solving")

	def simplify(self, e): # pylint:disable=R0201
		return e

	def add_exprs(self, s, c):
		return self.add(s, self.convert_exprs(c))

	def simplify_expr(self, e):
		o = self.simplify(self.convert_expr(e))
		return E(self._claripy, ast=self.abstract(o), objects={self: o}, variables=e.variables, symbolic=e.symbolic, length=e.length) # TODO: keep UUID

from ..expression import E, A
from ..operations import opposites
