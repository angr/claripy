import operator

import logging
l = logging.getLogger('claripy.backends.backend')

ops = { 'If', 'And', 'Not', 'Or', 'UGE', 'ULE', 'UGT', 'ULT', 'BoolVal', 'BitVec', 'BitVecVal', 'Concat', 'Extract', 'LShR', 'SignExt', 'ZeroExt', 'RotateLeft', 'RotateRight' }

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

	def process_arg(self, a, model=None): #pylint:disable=R0201
		return a.eval(backends=[self], model=model) if isinstance(a, E) else a

	def process_args(self, args, model=None):
		return [ self.process_arg(a, model=model) for a in args ]

	def call(self, name, args, model=None):
		'''
		Calls operation 'name' on 'obj' with arguments 'args'.

		@returns an Expression with the result.
		'''

		l.debug("%s.call(name=%s, args=%s)", self.__class__.__name__, name, args)

		if name in self._op_expr:
			return self._op_expr[name](*args, model=model)

		variables = reduce(operator.or_, (a.variables for a in args if isinstance(a, E)), set())
		symbolic = any((a.symbolic for a in args if isinstance(a, E)))
		op_args = self.process_args(args)
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

		r = E(self._claripy, variables=variables, symbolic=symbolic, obj=obj)
		l.debug("Returning expression %s", r)
		return r

	def abstract(self, e, split_on=None): #pylint:disable=W0613,R0201
		raise BackendError("backend doesn't implement abstract()")

	#
	# Solver support.
	#

	def solver(self): #pylint:disable=W0613,R0201
		raise BackendError("backend doesn't support solving")

	def add_constraints(self, s, c): #pylint:disable=W0613,R0201
		raise BackendError("backend doesn't support solving")

	def solve(self, s): #pylint:disable=W0613,R0201
		raise BackendError("backend doesn't support solving")

	def eval(self, s, expr, n, extra_constraints=None, model=None): #pylint:disable=W0613,R0201
		raise BackendError("backend doesn't support solving")

	def simplify(self, e): # pylint:disable=R0201
		return e

from ..expression import E, opposites
