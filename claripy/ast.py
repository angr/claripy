import logging
l = logging.getLogger("claripy.ast")

class A(object):
	'''
	An A(ST) tracks a tree of operations on arguments. It has the following methods:

		op: the operation that is being done on the arguments
		args: the arguments that are being used
		why: the reason that Claripy fell back to an AST instead of keeping things
			 as a model. BACKEND_ERROR means that no backend could handle the
			 opertaion, while DELAYED_OP means that the AST represents a delayed
			 operation on a possible model-handleable object.

	It also has the following useful members:

		size(): the size of the result
	'''

	__slots__ = [ 'op', 'args', 'why', '_length', '_hash', '__weakref__' ]
	BACKEND_ERROR = "BACKEND_ERROR"
	DELAYED_OP = "DELAYED_OP"

	def __init__(self, op, args, why=BACKEND_ERROR):
		self.op = op
		self.args = args
		self.why = why
		self._hash = None
		self._length = None

	@staticmethod
	def arg_size(backends, o):
		if isinstance(o, E):
			return o.size()
		elif isinstance(o, A):
			return o.size(backends=backends)
		else:
			for b in backends:
				try: return b.call('size', (o,))
				except BackendError: pass
			return -1

	def calculate_length(self, backends):
		if self.op in length_none_operations:
			return -1

		if self.op in length_same_operations:
			if self.op == 'If':
				lengths = set(self.arg_size(backends, a) for a in self.args[1:])
			else:
				lengths = set(self.arg_size(backends, a) for a in self.args)

			if len(lengths) != 1:
				raise ClaripySizeError("invalid length combination for operation %s" % self.op)
			return lengths.__iter__().next()

		if self.op in length_change_operations:
			if self.op in ( "SignExt", "ZeroExt" ):
				length = self.arg_size(backends, self.args[1])
				if length == -1: raise ClaripyTypeError("extending an object without a length")
				return length + self.args[0]
			if self.op == 'Concat':
				lengths = [ self.arg_size(backends, a) for a in self.args ]
				if len(lengths) != len(self.args) or -1 in lengths:
					raise ClaripyTypeError("concatenating an object without a length")
				return sum(lengths)
			if self.op == 'Extract':
				return self.args[0]-self.args[1]+1

		if self.op == 'BoolVal':
			return -1

		if self.op in length_new_operations:
			return self.args[1]

		raise ClaripyOperationError("unknown operation %s" % self.op)

	def size(self, backends=()):
		if self._length is None:
			self._length = self.calculate_length(backends)
		return self._length

	def resolve(self, b, save=None, result=None):
		if result is not None and self in result.resolve_cache[b]:
			return result.resolve_cache[b][self]

		args = [ ]
		for a in self.args:
			if isinstance(a, E):
				args.append(b.convert_expr(a, result=result))
			elif isinstance(a, A):
				args.append(a.resolve(b, save=save, result=result))
			else:
				args.append(b.convert(a, result=result))

		l.debug("trying evaluation with %s", b)
		r = b.call(self.op, args, result=result)
		if result is not None:
			result.resolve_cache[b][self] = r
		return r

	def __repr__(self):
		if '__' in self.op:
			return "%s.%s%s" % (self.args[0], self.op, self.args[1:])
		else:
			return "%s%s" % (self.op, self.args)

	def __hash__(self):
		if self._hash is None:
			self._hash = hash((self.op,) + tuple(self.args))
		return self._hash

	def __getstate__(self):
		return self.op, self.args
	def __setstate__(self, state):
		self._hash = None
		self.op, self.args = state

from .errors import BackendError, ClaripySizeError, ClaripyOperationError, ClaripyTypeError
from .operations import length_none_operations, length_change_operations, length_same_operations, length_new_operations
from .expression import E
