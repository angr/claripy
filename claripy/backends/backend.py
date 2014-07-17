import logging
l = logging.getLogger('claripy.backends.backend')
l.setLevel(logging.DEBUG)

ops = { 'If', 'And', 'Not', 'Or', 'UGE', 'ULE', 'UGT', 'ULT', 'BoolVal', 'BitVec', 'BitVecVal', 'Concat', 'Extract', 'LShR', 'SignExt', 'ZeroExt', 'RotateLeft', 'RotateRight' }

class BackendError(Exception):
	pass

class Backend(object):
	def __init__(self):
		self._op_raw = { }
		self._op_expr = { }

	def _make_raw_ops(self, op_list, op_dict=None, op_module=None):
		for o in op_list:
			op_func = op_dict[o] if op_dict is not None else getattr(op_module, o)
			self._op_raw[o] = self._make_raw_op(o, op_func)

	def _make_raw_op(self, op_name, op_func):
		def op(*args, **kwargs): #pylint:disable=W0613
			if hasattr(self, 'normalize_args'):
				normalized_args = getattr(self, 'normalize_args')(op_name, args)
			else:
				normalized_args = args

			return op_func(*normalized_args)
		return op

	def combined_info(self, args, model=None):
		op_args = [ ]
		variables = set()
		symbolic = False
		#abstract = False

		for a in args:
			if isinstance(a, E):
				variables |= a.variables
				symbolic |= a.symbolic
				op_args.append(a._obj)
			else:
				op_args.append(a)

		processed_args = self.process_args(op_args, args, model=model)
		return variables, symbolic, processed_args

	def process_args(self, args, exprs, model=None): #pylint:disable=R0201,W0613
		return args

	def call(self, name, args, model=None):
		'''
		Calls operation 'name' on 'obj' with arguments 'args'.

		@returns an Expression with the result.
		'''

		l.debug("call(name=%s, args=%s)", name, args)

		if name in self._op_expr:
			return self._op_expr[name](*args, model=model)

		variables, symbolic, op_args = self.combined_info(args, model=model)

		if name in self._op_raw:
			obj = self._op_raw[name](*op_args, model=model)
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

		r = E([self], variables=variables, symbolic=symbolic, obj=obj)
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

	def eval(self, s, expr, n, extra_constraints=None): #pylint:disable=W0613,R0201
		raise BackendError("backend doesn't support solving")

from ..expression import E, opposites
