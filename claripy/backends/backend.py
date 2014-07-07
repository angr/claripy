ops = [ 'If', 'And', 'Not', 'Or', 'UGE', 'ULE', 'UGT', 'ULT', 'BoolVal', 'BitVec', 'BitVecVal', 'Concat', 'Extract', 'LShR', 'SignExt', 'ZeroExt' ]

class Backend(object):
	def __init__(self):
		self.op_dict = { }

	def op(self, op_name):
		return self.op_dict[op_name]

	def _make_ops(self, op_list, op_dict=None, op_module=None):
		for o in op_list:
			op_func = op_dict[o] if op_dict is not None else getattr(op_module, o)
			self.op_dict[o] = self._make_op(o, op_func)

	def _make_op(self, op_name, op_func):
		def op(*args):
			if hasattr(self, 'normalize_args'):
				normalized_args = getattr(self, 'normalize_args')(op_name, args)
			else:
				normalized_args = args

			return op_func(*normalized_args)
		return op
