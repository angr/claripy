import logging
l = logging.getLogger("claripy.ast")

class A(object):
	'''
	An A(ST) tracks a tree of operations on arguments. It has the following methods:

		op: the operation that is being done on the arguments
		args: the arguments that are being used
		length: the length (in bits)

	It also has the following useful members:

		size(): the size of the result
	'''

	__slots__ = [ 'op', 'args', 'why', 'length', '_claripy', '_hash', '__weakref__' ]

	def __init__(self, claripy, op, args):
		self.op = op
		self.args = args
		self.length = None
		self._hash = None
		self._claripy = claripy

		if hasattr(self, 'finalize_'+self.op): getattr(self, 'finalize_'+self.op)()
		elif self.op in length_same_operations: self.finalize_same_length()
		elif self.op in length_none_operations: pass
		else: raise ClaripyOperationError("no A.finalize_* function found for %s" % self.op)

	#
	# Finalizer functions for different expressions
	#

	def finalize_BoolVal(self):
		if len(self.args) != 1 or self.args[0] not in (True, False):
			raise ClaripyOperationError("BoolVal() requires True or False as argument.")

	def finalize_BitVec(self):
		if len(self.args) != 2 or type(self.args[0]) is not str or type(self.args[1]) not in (int, long) or self.args[1] <= 0:
			raise ClaripyOperationError("Invalid arguments to BitVec")
		self.length = int(self.args[1])

	def finalize_BitVecVal(self):
		if len(self.args) != 2 or type(self.args[0]) not in (int, long) or type(self.args[1]) not in (int, long) or self.args[1] <= 0:
			raise ClaripyOperationError("Invalid arguments to BitVecVal")
		self.length = int(self.args[1])
		self.args = (self.args[0], int(self.args[1]))

	def finalize_If(self):
		'''
		An If requires a boolean condition, and at least one case with a length. If both
		cases have lengths, they must be equal.
		'''

		if len(self.args) != 3:
			raise ClaripyOperationError("If requires a condition and two cases.")
		lengths = set(self.arg_size(a) for a in self.args[1:]) - { None }
		if len(lengths) != 1 or self.arg_size(self.args[0]) is not None:
			raise ClaripyOperationError("If needs must have equal-sized cases and a boolean condition")
		self.length = lengths.pop()

	def finalize_Concat(self):
		lengths = [ self.arg_size(a) for a in self.args ]
		if None in lengths or len(self.args) <= 1:
			raise ClaripyOperationError("Concat must have at >= two args, and all must have lengths.")
		self.length = sum(lengths)

	def finalize_Extract(self):
		if len(self.args) != 3 or type(self.args[0]) not in (int, long) or type(self.args[1]) not in (int, long):
			raise ClaripyOperationError("Invalid arguments passed to extract!")

		self.args = (int(self.args[0]), int(self.args[1]), self.args[2])
		self.length = self.args[0]-self.args[1]+1

	def finalize_ZeroExt(self):
		if len(self.args) != 2 or type(self.args[0]) not in (int, long):
			raise ClaripyOperationError("%s requires two arguments: (int, bitvector)" % self.op)

		length = self.arg_size(self.args[1])
		if length is None:
			raise ClaripyOperationError("extending an object without a length")

		self.args = (int(self.args[0]), self.args[1])
		self.length = length + self.args[0]
	finalize_SignExt = finalize_ZeroExt

	# And generic ones

	def finalize_same_length(self):
		'''
		This is a generic finalizer. It requires at least one argument to have a length,
		and all arguments that *do* have a length to have the same length.
		'''

		lengths = set(self.arg_size(a) for a in self.args) - { None }
		if len(lengths) != 1:
			raise ClaripyOperationError("Arguments to %s must have equal (and existing) sizes", self.op)
		self.length = lengths.pop()



	def arg_size(self, o):
		if isinstance(o, E):
			return o.size()
		elif isinstance(o, A):
			return o.length
		else:
			for b in self._claripy.model_backends:
				try: return b.call('size', (o,))
				except BackendError: pass
			return None

	def size(self):
		return self.length

	def resolve(self, b, save=None, result=None):
		if result is not None and self in result.resolve_cache[b]:
			return result.resolve_cache[b][self]

		args = [ ]
		for a in self.args:
			if isinstance(a, E):
				args.append(b.convert_expr(a, result=result))
			elif isinstance(a, A):
				args.append(a.resolve(b, save=save, result=result)) #pylint:disable=maybe-no-member
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
		return self.op, self.args, self.length
	def __setstate__(self, state):
		self._hash = None
		self.op, self.args, self.length = state

from .errors import BackendError, ClaripyOperationError
from .operations import length_none_operations, length_same_operations
from .expression import E
