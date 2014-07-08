import logging
l = logging.getLogger('claripy.backends.backend')
l.setLevel(logging.DEBUG)

ops = { 'If', 'And', 'Not', 'Or', 'UGE', 'ULE', 'UGT', 'ULT', 'BoolVal', 'BitVec', 'BitVecVal', 'Concat', 'Extract', 'LShR', 'SignExt', 'ZeroExt' }

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
		def op(*args):
			if hasattr(self, 'normalize_args'):
				normalized_args = getattr(self, 'normalize_args')(op_name, args)
			else:
				normalized_args = args

			return op_func(*normalized_args)
		return op

	@staticmethod
	def combined_info(args):
		op_args = [ ]
		variables = set()
		symbolic = False
		#abstract = False

		for a in args:
			if isinstance(a, E):
				variables |= a.variables
				symbolic |= a.symbolic
				op_args.append(a._obj)
			elif type(a) in { str, int, long }:
				op_args.append(a)
			else:
				raise TypeError("invalid type passed to Backend.call()")

		return variables, symbolic, op_args


	def call(self, name, args):
		'''
		Calls operation 'name' on 'obj' with arguments 'args'.

		@returns an Expression with the result.
		'''

		if name in self._op_expr:
			return self._op_expr[name](*args)

		variables, symbolic, op_args = self.combined_info(args)

		if name in self._op_raw:
			obj = self._op_raw[name](*op_args)
		else:
			op = getattr(op_args[0], name)
			obj = op(*op_args[1:])
		r = E([self], variables, symbolic, obj=obj)
		l.debug("Returning expression %s", r)
		return r

from ..expression import E
