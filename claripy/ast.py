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

	__slots__ = [ 'op', 'args', 'why', 'length', 'collapsible', '_claripy', '_hash', '__weakref__' ]

	def __init__(self, claripy, op, args, collapsible=False):
		self.op = op
		self.args = args
		self.length = None
		self.collapsible = collapsible
		self._hash = None
		self._claripy = claripy

		if hasattr(self, 'finalize_'+self.op): getattr(self, 'finalize_'+self.op)()
		elif self.op in length_same_operations: self.finalize_same_length()
		elif self.op in length_none_operations: pass
		else: raise ClaripyOperationError("no A.finalize_* function found for %s" % self.op)

		if self.length is not None and self.length < 0:
			raise ClaripyOperationError("length is negative!")

		#if self.op == 'Reverse':
		#	a = self.args[0]
		#	if isinstance(a, E): a = a.ast
		#	if isinstance(a, A) and a.op == 'Reverse':
		#		raise ClaripyOperationError("wtf, reverse")

	#
	# Finalizer functions for different expressions
	#

	def finalize_Identical(self):
		self.length = 0

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

		if self.length > self.arg_size(self.args[2]) or \
						self.args[0] >= self.arg_size(self.args[2]) or \
						self.args[1] >= self.arg_size(self.args[2]) or \
						self.length <= 0:
			raise ClaripyOperationError("Invalid arguments passed to extract!")

	def finalize_ZeroExt(self):
		if len(self.args) != 2 or type(self.args[0]) not in (int, long) or self.args[0] < 0:
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

	def resolve(self, b, result=None):
		if result is not None and self in result.resolve_cache[b]:
			return result.resolve_cache[b][self]

		args = [ ]
		#pylint:disable=maybe-no-member
		for a in self.args:
			if isinstance(a, A):
				if self.op == 'Reverse' and a.op == 'Reverse':
					return a.args[0]
				args.append(a.resolve(b, result=result))
			else:
				args.append(a)
		#pylint:enable=maybe-no-member

		l.debug("trying evaluation with %s", b)
		r = b.call_expr(self.op, args, result=result)
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
			self._hash = hash((self.op, tuple(self.args), self._claripy.name))
		return self._hash

	def __getstate__(self):
		return self.op, self.args, self.length
	def __setstate__(self, state):
		self._hash = None
		self.op, self.args, self.length = state

	@property
	def variables(self):
		v = set()
		for a in self.args:
			if isinstance(a, E):
				v |= a.variables #pylint:disable=maybe-no-member
		return v

	@property
	def symbolic(self):
		return any([ a.symbolic for a in self.args if isinstance(a, E) ]) #pylint:disable=maybe-no-member

	def _replace(self, old, new):
		if hash(self) == hash(old.ast):
			return new.ast, True

		new_args = [ ]
		replaced = False

		for a in self.args:
			if isinstance(a, A):
				new_a, a_replaced = a._replace(old, new) #pylint:disable=maybe-no-member
			elif isinstance(a, E):
				new_a, a_replaced = a._replace(old, new) #pylint:disable=maybe-no-member
			else:
				new_a, a_replaced = a, False

			new_args.append(new_a)
			replaced |= a_replaced

		if replaced:
			return A(self._claripy, self.op, tuple(new_args)), True
		else:
			return self, False

	@staticmethod
	def _reverse_op(op):
		if op == 'ULE':
			return 'UGE'

		raise Exception()

	@staticmethod
	def reverse_operation(target, op, args, index):
		'''

		:param target:
		:param op:
		:param args:
		:return: a reversed ast
		'''
		if op == 'Extract':
			# FIXME:
			left = args[0]
			right = args[1]
			if right != 0:
				return None
			original_size = args[index].size()
			return target.zero_extend(original_size - (left - right + 1))
		elif op == 'ZeroExt':
			# FIXME:
			extra_bits = args[0]
			return target[target.size() - extra_bits  - 1: 0]

		import ipdb; ipdb.set_trace()
		return None


	def find_arg(self, arg):
		for index, a in enumerate(self.args):
			if a is arg:
				return [index]

		tuple_list = None
		for index, a in enumerate(self.args):
			if type(a) is E and type(a.ast) is A:
				tuple_list = a.ast.find_arg(arg)
				if tuple_list is not None:
					tuple_list = [index] + tuple_list
					break

		return tuple_list

	def pivot(self, left=None, right=None):
		'''

		:param left:
		:param right:
		:return:
		'''
		if left is None and right is None:
			return

		if left is not None and right is not None:
			raise ClaripyOperationError('You cannot specify two endpoints on both sides')

		if len(self.args) != 2:
			raise ClaripyOperationError('We cannot pivot an operation that has over two arguments')

		op = self.op
		arg_left = self.args[0]
		arg_right = self.args[1]

		if left is None:
			# Swap it
			left, right = right, left
			arg_left, arg_right = arg_right, arg_left
			op = A._reverse_op(op)

		arg_index_list = arg_left.ast.find_arg(left)
		if arg_index_list is None:
			raise ClaripyOperationError('Cannot find argument %s' % left)

		for index in arg_index_list:
			left_ast_args = arg_left.ast.args
			arg_right = A.reverse_operation(arg_right, arg_left.ast.op, left_ast_args, index)
			if arg_right is None:
				raise ClaripyOperationError('Pivoting failed.')
			arg_left = arg_left.ast.args[index]

		new_ast = A(self._claripy, op, (arg_left, arg_right))
		return new_ast

from .errors import BackendError, ClaripyOperationError
from .operations import length_none_operations, length_same_operations
from .expression import E
