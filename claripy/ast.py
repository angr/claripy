import weakref
import logging
l = logging.getLogger("claripy.ast")

import ana

class A(ana.Storable):
	'''
	An A(ST) tracks a tree of operations on arguments. It has the following methods:

		op: the operation that is being done on the arguments
		args: the arguments that are being used
		length: the length (in bits)

	It also has the following useful members:

		size(): the size of the result
	'''

	__slots__ = [ 'op', 'args', 'length', 'variables', 'symbolic', '_objects', '_collapsible', '_claripy', '_hash', '_simplified', '_objects', '_errored' ]
	_hash_cache = weakref.WeakValueDictionary()

	FULL_SIMPLIFY=1
	LITE_SIMPLIFY=2
	UNSIMPLIFIED=0

	def __new__(cls, claripy, op, args, **kwargs):
		h = cls._calc_hash(claripy, op, args)
		if h in cls._hash_cache:
			return cls._hash_cache[h]
		else:
			self = super(A, cls).__new__(cls, claripy, op, args, **kwargs)
			cls._hash_cache[h] = self
			return self

	def __init__(self, claripy, op, args, variables=None, symbolic=None, length=None, collapsible=None, finalize=True, simplified=0, errored=None):
		try:
			# already been initialized, and the stupid __new__ call is calling it again...
			op = self.op # pylint:disable=access-member-before-definition
			return
		except AttributeError:
			pass

		self.op = op
		self.args = args
		self.length = length
		self._collapsible = True if collapsible is None else collapsible
		self._hash = None
		self._claripy = claripy

		self._objects = { }
		self._simplified = simplified

		if len(args) == 0:
			raise ClaripyOperationError("AST with no arguments!")

		self.variables = set.union(set(), *(a.variables for a in args if isinstance(a, A))) if variables is None else variables
		self._errored = set.union(set(), *(a._errored for a in args if isinstance(a, A))) if errored is None else errored
		self.symbolic = any((a.symbolic for a in args if isinstance(a, A))) if symbolic is None else symbolic

		if finalize:

			if hasattr(self, '_finalize_'+self.op): getattr(self, '_finalize_'+self.op)()
			elif self.op in length_same_operations: self._finalize_same_length()
			elif self.op in length_none_operations: pass
			else: raise ClaripyOperationError("no A._finalize_* function found for %s" % self.op)

			if self.length is not None and self.length < 0:
				raise ClaripyOperationError("length is negative!")

	@property
	def uuid(self):
		return self.ana_uuid

	@staticmethod
	def _calc_hash(clrp, op, args):
		return hash((op, tuple(args), clrp.name))

	def __hash__(self):
		if self._hash is None:
			self._hash = self._calc_hash(self._claripy, self.op, self.args)
		return self._hash

	#
	# Collapsing and simplification
	#

	#def _models_for(self, backend):
	#	for a in self.args:
	#		backend.convert_expr(a)
	#		else:
	#			yield backend.convert(a)

	def _should_collapse(self):
		raw_args = self.arg_models()
		types = [ type(a) for a in raw_args ]

		#l.debug("In should_collapse()")

		if types.count(A) != 0 and not all((a._collapsible for a in raw_args if isinstance(a, A))):
				#l.debug("... not collapsing for op %s because ASTs are present.", self.op)
				return False

		if self.op in not_invertible:
			#l.debug("... collapsing the AST for operation %s because it's not invertible", self.op)
			return True

		constants = sum((types.count(t) for t in (int, long, bool, str, BVV)))
		if constants == len(raw_args):
			#l.debug("... collapsing the AST for operation %s because it's full of constants", self.op)
			return True

		if len([ a for a in raw_args if isinstance(a, StridedInterval) and a.is_integer()]) > 1:
			#l.debug("... collapsing the AST for operation %s because there are more than two SIs", self.op)
			return True

		#
		# More complex checks probably go here.
		#

		# Reversible; don't collapse!
		#l.debug("not collapsing the AST for operation %s!", self.op)
		return False

	@property
	def collapsed(self):
		if self._should_collapse() and self._collapsible:
			#l.debug("Collapsing!")
			r = self.model
			if not isinstance(r, A):
				return I(self._claripy, r, length=self.length, finalize=False, variables=self.variables, symbolic=self.symbolic)
			else:
				return r
		else:
			return self

	@property
	def simplified(self):
		if self.op == 'Reverse' and isinstance(self.args[0], A) and self.args[0].op == 'Reverse':
			return self.args[0].args[0]

		if self.op in reverse_distributable and all((isinstance(a, A) for a in self.args)) and set((a.op for a in self.args)) == { 'Reverse' }:
			inner_a = A(self._claripy, self.op, tuple(a.args[0] for a in self.args)).simplified
			o = A(self._claripy, 'Reverse', (inner_a,), collapsible=True).simplified
			o._simplified = A.LITE_SIMPLIFY
			return o

		return self

	@property
	def reduced(self):
		a = self.simplified
		if isinstance(a, A):
			return a.collapsed
		else:
			return a

	#
	# Finalizer functions for different expressions
	#

	@staticmethod
	def _typefixer(a, t):
		if t in ('I', 'L', 'N'):
			if not type(a) in (int, long):
				raise ClaripyOperationError("argument is not the right type (%s instead of int/long)" % type(a))
			return int(a) if t == 'I' else long(a) if t == 'L' else a
		else:
			if not isinstance(a, t):
				raise ClaripyOperationError("argument is not the right type (%s instead of int/long)" % type(a))
			return a

	def _typechecker(self, *types):
		if len(self.args) != len(types):
			raise ClaripyOperationError("too few arguments (%d instead of %d) passed to %s" % (len(self.args), len(types), self.op))

		self.args = tuple(self._typefixer(a,t) for a,t in zip(self.args, types))

	def _finalize_Identical(self):
		self.length = 0

	def _finalize_BoolVal(self):
		self._typechecker(bool)

	def _finalize_BitVec(self):
		self._typechecker(str, 'I')
		self.length = self.args[1]

	def _finalize_BitVecVal(self):
		self._typechecker('N', 'I')
		if self.args[1] <= 0:
			raise ClaripyOperationError("Invalid arguments to BitVecVal")
		self.length = self.args[1]

	def _finalize_If(self):
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

	def _finalize_Concat(self):
		lengths = [ self.arg_size(a) for a in self.args ]
		if None in lengths or len(self.args) <= 1:
			raise ClaripyOperationError("Concat must have at >= two args, and all must have lengths.")
		self.length = sum(lengths)

	def _finalize_Extract(self):
		self._typechecker('I', 'I', A)
		if len(self.args) != 3 or type(self.args[0]) not in (int, long) or type(self.args[1]) not in (int, long):
			raise ClaripyOperationError("Invalid arguments passed to extract!")

		self.length = self.args[0]-self.args[1]+1
		old_length = self.arg_size(self.args[2])
		if self.length > old_length or self.args[0] >= old_length or self.args[1] >= old_length or self.length <= 0:
			raise ClaripyOperationError("Invalid sizes passed to extract!")

	def _finalize_ZeroExt(self):
		self._typechecker('I', A)
		length = self.arg_size(self.args[1])
		if length is None:
			raise ClaripyOperationError("extending an object without a length")
		self.length = length + self.args[0]
	_finalize_SignExt = _finalize_ZeroExt

	def _finalize_same_length(self):
		'''
		This is a generic finalizer. It requires at least one argument to have a length,
		and all arguments that *do* have a length to have the same length.
		'''

		lengths = set(self.arg_size(a) for a in self.args) - { None }
		if len(lengths) != 1:
			raise ClaripyOperationError("Arguments to %s must have equal (and existing) sizes", self.op)
		self.length = lengths.pop()

	#
	# Size functions
	#

	@staticmethod
	def arg_size(o):
		if isinstance(o, A):
			return o.length
		else:
			return None

	def size(self):
		return self.length
	__len__ = size

	#
	# Functionality for resolving to model objects
	#

	def arg_models(self):
		return [ (a.model if isinstance(a, A) else a) for a in self.args ]

	def resolved(self, result=None):
		for b in self._claripy.model_backends:
			try: return self.resolved_with(b, result=result)
			except BackendError: self._errored.add(b)
		l.debug("all model backends failed for op %s", self.op)
		return self

	@property
	def model(self):
		return self.resolved()

	def resolved_with(self, b, result=None):
		if b in self._objects:
			return self._objects[b]

		if b in self._errored and result is None:
			raise BackendError("%s already failed" % b)

		if result is not None and self in result.resolve_cache[b]:
			return result.resolve_cache[b][self]

		#l.debug("trying evaluation with %s", b)
		r = b.call(self, result=result)
		if result is not None:
			result.resolve_cache[b][self] = r
		else:
			self._objects[b] = r
		return r

	#
	# Viewing and debugging
	#

	def __repr__(self):
		if '__' in self.op:
			return "<A %s.%s%s>" % (self.args[0], self.op, self.args[1:])
		else:
			return "<A %s%s>" % (self.op, self.args)

	@property
	def depth(self):
		return 1 + max((a.depth() for a in self.args if isinstance(a, A)))

	#
	# Serialization support
	#

	def _ana_getstate(self):
		return self.op, self.args, self.length, self.variables, self.symbolic, self._claripy.name
	def _ana_setstate(self, state):
		op, args, length, variables, symbolic, clrp = state
		A.__init__(self, Claripies[clrp], op, args, length=length, variables=variables, symbolic=symbolic)

	#
	# Various AST modifications (replacements, pivoting)
	#

	def _do_op(self, op, *args, **kwargs):
		return A(self._claripy, op, (self,)+args, **kwargs).reduced

	def _replace(self, old, new):
		if hash(self) == hash(old):
			return new, True

		new_args = [ ]
		replaced = False

		for a in self.args:
			if isinstance(a, A):
				new_a, a_replaced = a._replace(old, new) #pylint:disable=maybe-no-member
			else:
				new_a, a_replaced = a, False

			new_args.append(new_a)
			replaced |= a_replaced

		if replaced:
			return A(self._claripy, self.op, tuple(new_args)).reduced, True
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
			if isinstance(a, A):
				tuple_list = a.find_arg(arg)
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

		arg_index_list = arg_left.find_arg(left)
		if arg_index_list is None:
			raise ClaripyOperationError('Cannot find argument %s' % left)

		for index in arg_index_list:
			left_ast_args = arg_left.args
			arg_right = A.reverse_operation(arg_right, arg_left.op, left_ast_args, index)
			if arg_right is None:
				raise ClaripyOperationError('Pivoting failed.')
			arg_left = arg_left.args[index]

		new_ast = A(self._claripy, op, (arg_left, arg_right))
		return new_ast

	#
	# Other helper functions
	#

	def split(self, split_on):
		if self.op in split_on: return list(self.args)
		else: return [ self ]

	# we don't support iterating over A objects
	def __iter__(self):
		raise ClaripyOperationError("Please don't iterate over, or split, AST nodes!")

	def __nonzero__(self):
		raise ClaripyOperationError('testing Expressions for truthiness does not do what you want, as these expressions can be symbolic')

	def chop(self, bits=1):
		s = len(self)
		if s % bits != 0:
			raise ValueError("expression length (%d) should be a multiple of 'bits' (%d)" % (len(self), bits))
		elif s == bits:
			return [ self ]
		else:
			return list(reversed([ self[(n+1)*bits - 1:n*bits] for n in range(0, s / bits) ]))

	@property
	def reversed(self):
		'''
		Reverses the expression.
		'''
		return self._do_op('Reverse', collapsible=False)

	def __getitem__(self, rng):
		if type(rng) is slice:
			return self._claripy.Extract(int(rng.start), int(rng.stop), self)
		else:
			return self._claripy.Extract(int(rng), int(rng), self)

	def zero_extend(self, n):
		return self._claripy.ZeroExt(n, self)

	def sign_extend(self, n):
		return self._claripy.SignExt(n, self)

	def identical(self, o):
		return self._claripy.is_identical(self, o)

	def replace(self, old, new):
		if not isinstance(old, A) or not isinstance(new, A):
			raise ClaripyOperationError('replacements must be AST nodes')
		if old.size() != new.size():
			raise ClaripyOperationError('replacements must have matching sizes')
		return self._replace(old, new)[0]

class I(A):
	'''
	This is an 'identity' AST -- it acts as a wrapper around model objects.
	'''

	def __new__(cls, claripy, model, **kwargs):
		return A.__new__(cls, claripy, 'I', (model,), **kwargs)
	def __init__(self, claripy, model, **kwargs):
		A.__init__(self, claripy, 'I', (model,), **kwargs)

	def resolved(self, result=None): return self.args[0]
	def resolved_with(self, b, result=None): return b.convert(self.args[0])
	@property
	def depth(self): return 0
	def split(self, split_on): return self
	def _finalize_I(self):
		for b in self._claripy.model_backends:
			try:
				self.length = b.size(self.args[0])
				break
			except BackendError: pass
		else:
			self.length = None

from .errors import BackendError, ClaripyOperationError
from .operations import length_none_operations, length_same_operations, reverse_distributable, not_invertible
from .bv import BVV
from .vsa import StridedInterval
from . import Claripies


#
# Overload the operators
#

def e_operator(cls, op_name):
	def wrapper(self, *args):
		return self._do_op(op_name, *args)
	wrapper.__name__ = op_name
	setattr(cls, op_name, wrapper)

def make_methods():
	for name in expression_operations:
		e_operator(A, name)

from .operations import expression_operations
make_methods()
