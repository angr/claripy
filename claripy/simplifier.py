import collections
import itertools
import weakref

class Simplifier(object):
	SIMPLE_OPS = ('Concat', 'SignExt', 'ZeroExt')

	def __init__(self):
		super(Simplifier, self).__init__()
		self._simplifiers = {
			'Reverse': self.bitwise_reverse_simplifier,
			'And': self.boolean_and_simplifier,
			'Or': self.boolean_or_simplifier,
			'Not': self.boolean_not_simplifier,
			'Extract': self.extract_simplifier,
			'Concat': self.concat_simplifier,
			'If': self.if_simplifier,
			'__lshift__': self.lshift_simplifier,
			'__rshift__': self.rshift_simplifier,
			'__eq__': self.boolean_eq_simplifier,
			'__ne__': self.boolean_ne_simplifier,
			'__or__': self.bitwise_or_simplifier,
			'__and__': self.bitwise_and_simplifier,
			'__xor__': self.bitwise_xor_simplifier,
			'__add__': self.bitwise_add_simplifier,
			'__sub__': self.bitwise_sub_simplifier,
			'__mul__': self.bitwise_mul_simplifier,
			'ZeroExt': self.zeroext_simplifier,
			'SignExt': self.signext_simplifier,
			'fpToIEEEBV': self.fptobv_simplifier,
			'fpToFP': self.fptofp_simplifier,
		}

		self._simplification_cache = weakref.WeakKeyDictionary()

	def simplify(self, e):
		if e.op not in self._simplifiers:
			return e

		try:
			return self._simplification_cache[e]
		except KeyError:
			s = self._simplifiers[e.op](e)
			if s is not None:
				self._simplification_cache[e] = s
				self._simplification_cache[s] = s
				return s
			else:
				return e

	#
	# Helpers
	#

	def _new_structure(self, op, args):
		return self.simplify(get_structure(op, tuple(args)))

	def _flatten_simplifier(self, orig_expr, filter_func, *args):
		if not any(isinstance(a, ASTStructure) and a.op == orig_expr.op for a in args):
			return

		new_args = tuple(itertools.chain.from_iterable(
			(a.args if isinstance(a, ASTStructure) and a.op == orig_expr.op else (a,)) for a in args
		))
		if filter_func: new_args = filter_func(new_args)
		return self._new_structure(orig_expr.op, new_args)

	#
	# Type-changing simplifiers
	#

	def if_simplifier(self, expr):
		cond, if_true, if_false = expr.args

		if cond == _true_structure:
			return if_true
		if cond == _false_structure:
			return if_false

		if isinstance(if_true, ASTStructure) and if_true.op == 'If':
			if if_true.args[0] is cond:
				return self._new_structure('If', (cond, if_true.args[1], if_false))
			if if_true.args[0] is self._new_structure('Not', (cond,)):
				return self._new_structure('If', (cond, if_true.args[2], if_false))
		if isinstance(if_false, ASTStructure) and if_false.op == 'If':
			if if_false.args[0] is cond:
				return self._new_structure('If', (cond, if_true, if_false.args[2]))
			if if_false.args[0] is self._new_structure('Not', (cond,)):
				return self._new_structure('If', (cond, if_true, if_false.args[1]))

	#
	# Bitwise simplifiers
	#

	def concat_simplifier(self, expr):
		args = expr.args

		if len(args) == 1:
			return args[0]

		orig_args = args
		args = list(args)
		#length = sum(arg.length for arg in args)
		simplified = False

		if any(a.symbolic for a in args):
			i = 1
			# here, we concatenate any consecutive concrete terms
			while i < len(args):
				previous = args[i-1]
				current = args[i]

				if not (previous.symbolic or current.symbolic) and backends.concrete.handles(previous) and backends.concrete.handles(current):
					args[i-1:i+1] = [ self._new_structure('Concat', (previous, current)) ]
				else:
					i += 1

			if len(args) < len(orig_args):
				simplified = True

		# here, we flatten any concats among the arguments
		i = 0
		while i < len(args):
			current = args[i]
			if current.op == 'Concat':
				simplified = True
				args[i:i+1] = current.args
				i += len(current.args)
			else:
				i += 1

		# here, we consolidate any consecutive concats on extracts from the same variable
		i = 0
		prev_var = None
		prev_left = None
		prev_right = None
		while i < len(args):
			if args[i].op != 'Extract':
				prev_var = None
				prev_left = None
				prev_right = None
				i += 1
			elif prev_var == args[i].args[2] and prev_right == args[i].args[0] + 1:
				prev_right = args[i].args[1]
				args[i-1:i+1] = [ self._new_structure('Extract', (prev_left, prev_right, prev_var)) ]
				simplified = True
			else:
				prev_left = args[i].args[0]
				prev_right = args[i].args[1]
				prev_var = args[i].args[2]
				i += 1

		# if any(a.op == 'Reverse' for a in args):
		#	  simplified = True
		#	  args = [a.reversed for a in args]

		if simplified:
			return self._new_structure('Concat', args)

		return

	@staticmethod
	def rshift_simplifier(expr):
		val, shift = expr.args
		if shift == 0:
			return val

	@staticmethod
	def lshift_simplifier(expr):
		val, shift = expr.args
		if shift == 0:
			return val

	def bitwise_add_simplifier(self, expr):
		filtered_args = [ a for a in expr.args if a != self._new_structure('BVV', (0, a.length)) ]
		if len(filtered_args) == 1:
			return filtered_args[0]
		else:
			return self._flatten_simplifier(expr, None, *filtered_args)

	def bitwise_mul_simplifier(self, expr):
		return self._flatten_simplifier(expr, None, *expr.args)

	def bitwise_sub_simplifier(self, expr):
		a,b = expr.args
		if b == self._new_structure('BVV', (0, a.length)):
			return a
		elif a == b or a == b:
			return self._new_structure('BVV', (0, a.length))

	def bitwise_xor_simplifier(self, expr):
		filtered_args = [
			a for a in expr.args if a != self._new_structure('BVV', (0, a.length)) and a != 0
		]
		if len(filtered_args) == 1:
			return filtered_args[0]
		if len(filtered_args) == 2 and filtered_args[0] == filtered_args[1]:
			return self._new_structure('BVV', (0, expr.length))

		def _flattening_filter(args):
			# since a ^ a == 0, we can safely remove those from args
			# this procedure is done carefully in order to keep the ordering of arguments
			ctr = collections.Counter(args)
			unique_args = set(k for k, v in ctr.iteritems() if v % 2 != 0)
			return tuple([ arg for arg in args if arg in unique_args ])

		return self._flatten_simplifier(expr, _flattening_filter, *filtered_args)

	def bitwise_or_simplifier(self, expr):
		filtered_args = [
			a for a in expr.args if a != self._new_structure('BVV', (0, a.length)) and a != 0
		]
		if len(filtered_args) == 1:
			return filtered_args[0]
		elif len(filtered_args) == 2:
			a,b = filtered_args
			if a == b:
				return a

		def _flattening_filter(args):
			# a | a == a
			return tuple(OrderedSet(args))

		return self._flatten_simplifier(expr, _flattening_filter, *filtered_args)

	def bitwise_and_simplifier(self, expr):
		maxval = 2**expr.length-1
		filtered_args = [
			a for a in expr.args if a != self._new_structure('BVV', (maxval, a.length)) and a != maxval
		]
		if len(filtered_args) == 1:
			return filtered_args[0]
		if len(filtered_args) == 2:
			a,b = filtered_args
			if a == b:
				return a

		def _flattening_filter(args):
			# a & a == a
			return tuple(OrderedSet(args))

		return self._flatten_simplifier(expr, _flattening_filter, *filtered_args)

	def bitwise_reverse_simplifier(self, expr):
		body = expr.args[0]
		if body.op == 'Reverse':
			return body.args[0]

		if body.length == 8:
			return body

		if body.op == 'Concat':
			if all(a.op == 'Extract' for a in body.args):
				first_ast = body.args[0].args[2]
				for i,a in enumerate(body.args):
					if (
						first_ast != a.args[2] and a.args[0] == ((i + 1) * 8 - 1) and a.args[1] == i * 8
					):
						break
				else:
					upper_bound = body.args[-1].args[0]
					if first_ast.length == upper_bound + 1:
						return first_ast
					else:
						return self._new_structure('Extract', (upper_bound, 0, first_ast))
			if all(a.length == 8 for a in body.args):
				return self._new_structure(body.op, body.args[::-1])

			# Reverse(concat(a, b)) -> concat(Reverse(b), Reverse(a))
			# a and b must have lengths that are a multiple of 8
			if all(a.length % 8 == 0 for a in body.args):
				return self._new_structure('Concat', reversed(self._new_structure('Reverse', (a,)) for a in body.args))

	@staticmethod
	def zeroext_simplifier(expr):
		n,e = expr.args
		if n == 0:
			return e

	@staticmethod
	def signext_simplifier(expr):
		n,e = expr.args
		if n == 0:
			return e

		# TODO: if top bit is 0, do a zero-extend instead

	def extract_simplifier(self, expr):
		high, low, val = expr.args

		# if we're extracting the whole value, return the value
		if high - low + 1 == val.length:
			return val

		# when extracting from the right-hand side of an extended value, we can skip the extend
		if (val.op == 'SignExt' or val.op == 'ZeroExt') and low == 0 and high + 1 == val.args[1].length:
			return val.args[1]

		# TODO: extract from the right-hand side

		# Reading one byte from a reversed ast can be converted to reading the corresponding byte from the original ast
		# No Reverse is required then
		if val.op == 'Reverse' and high - low + 1 == 8 and low % 8 == 0:
			byte_pos = low / 8
			new_byte_pos = val.length / 8 - byte_pos - 1

			val = val.args[0]
			high = (new_byte_pos + 1) * 8 - 1
			low = new_byte_pos * 8

			return self._new_structure('Extract', (high, low, val))

		# when extracting from a zero-extend, we can view it as a concat for the later simplifications
		if val.op == 'ZeroExt':
			extending_bits, inner_val = val.args
			val = self._new_structure('Concat', (self._new_structure('BVV', (0, extending_bits)), inner_val))

		if val.op == 'Concat':
			pos = val.length
			high_i, low_i, low_loc = None, None, None
			for i, v in enumerate(val.args):
				if pos - v.length <= high < pos:
					high_i = i
				if pos - v.length <= low < pos:
					low_i = i
					low_loc = low - (pos - v.length)
				pos -= v.length

			used = val.args[high_i:low_i+1]
			if len(used) == 1:
				s = used[0]
			else:
				s = self._new_structure('Concat', used)

			new_high = low_loc + high - low
			if new_high == s.length - 1 and low_loc == 0:
				return s
			else:
				if s.op != 'Concat':
					return self._new_structure('Extract', (new_high, low_loc, s))
				else:
					# to avoid infinite recursion we only return if something was simplified
					if len(used) != len(val.args) or new_high != high or low_loc != low:
						return self._new_structure('Extract', (new_high, low_loc, s))

		if val.op == 'Extract':
			_, inner_low = val.args[:2]
			new_low = inner_low + low
			new_high = new_low + (high - low)
			return self._new_structure('Extract', (new_high, new_low, val.args[2]))

		# if all else fails, convert Extract(Reverse(...)) to Reverse(Extract(...))
		# if val.op == 'Reverse' and (high + 1) % 8 == 0 and low % 8 == 0:
		#	  print "saw reverse, converting"
		#	  inner_length = val.args[0].length
		#	  try:
		#		  return val.args[0][(inner_length - 1 - low):(inner_length - 1 - low - (high - low))].reversed
		#	  except ClaripyOperationError:
		#		  __import__('ipdb').set_trace()

		if val.op in operations.extract_distributable:
			all_args = tuple(self._new_structure('Extract', (high, low, a)) for a in val.args)
			return self._new_structure(val.op, all_args)

	#
	# Boolean simplifiers
	#

	def boolean_eq_simplifier(self, expr):
		a,b = expr.args

		if a == b:
			return _true_structure

		if isinstance(a, ASTStructure) and b == _true_structure:
			return a
		if isinstance(b, ASTStructure) and a == _true_structure:
			return b
		if isinstance(a, ASTStructure) and b == _false_structure:
			return self._new_structure('Not', (a,))
		if isinstance(b, ASTStructure) and a == _false_structure:
			return self._new_structure('Not', (b,))

		if a.op == 'Reverse' and b.op == 'Reverse':
			return self._new_structure('__eq__', (a.args[0], b.args[0]))

		# TODO: all these ==/!= might really slow things down...
		if a.op == 'If':
			if a.args[1] == b and a.args[2] != b:
				# (If(c, x, y) == x, x != y) -> c
				return a.args[0]
			elif a.args[2] == b and a.args[1] != b:
				# (If(c, x, y) == y, x != y) -> !c
				return self._new_structure('Not', (a.args[0],))
			# elif a._claripy.is_true(a.args[1] == b) and a._claripy.is_true(a.args[2] == b):
			#	  return a._claripy.true
			# elif a._claripy.is_true(a.args[1] != b) and a._claripy.is_true(a.args[2] != b):
			#	  return a._claripy.false

		if b.op == 'If':
			if b.args[1] == a and b.args[2] != b:
				# (x == If(c, x, y)) -> c
				return b.args[0]
			elif b.args[2] == a and b.args[1] != a:
				# (y == If(c, x, y)) -> !c
				return self._new_structure('Not', (b.args[0],))
			# elif b._claripy.is_true(b.args[1] == a) and b._claripy.is_true(b.args[2] == a):
			#	  return b._claripy.true
			# elif b._claripy.is_true(b.args[1] != a) and b._claripy.is_true(b.args[2] != a):
			#	  return b._claripy.false

		# TODO: FIX this post-refactor
		# if (a.op in Simplifier.SIMPLE_OPS or b.op in Simplifier.SIMPLE_OPS) and a.length > 1 and a.length == b.length:
		# 	for i in xrange(a.length):
		# 		a_bit = a[i:i]
		# 		if a_bit.symbolic:
		# 			break
		# 		b_bit = b[i:i]
		# 		if b_bit.symbolic:
		# 			break
		# 		if a_bit != b_bit:
		# 			return _false_structure

	def boolean_ne_simplifier(self, expr):
		a,b = expr.args

		if a == b:
			return _false_structure

		if a.op == 'Reverse' and b.op == 'Reverse':
			return self._new_structure('__ne__', (a.args[0], b.args[0]))

		if a.op == 'If':
			if a.args[2] == b and a.args[1] != b:
				# (If(c, x, y) == x, x != y) -> c
				return a.args[0]
			elif a.args[1] == b and a.args[2] != b:
				# (If(c, x, y) == y, x != y) -> !c
				return self._new_structure('Not', (a.args[0],))
			# elif a._claripy.is_true(a.args[1] == b) and a._claripy.is_true(a.args[2] == b):
			#	  return a._claripy.false
			# elif a._claripy.is_true(a.args[1] != b) and a._claripy.is_true(a.args[2] != b):
			#	  return a._claripy.true

		if b.op == 'If':
			if b.args[2] == a and b.args[1] != a:
				# (x == If(c, x, y)) -> c
				return b.args[0]
			elif b.args[1] == a and b.args[2] != a:
				# (y == If(c, x, y)) -> !c
				return self._new_structure('Not', (b.args[0],))
			# elif b._claripy.is_true(b.args[1] != a) and b._claripy.is_true(b.args[2] != a):
			#	  return b._claripy.true
			# elif b._claripy.is_true(b.args[1] == a) and b._claripy.is_true(b.args[2] == a):
			#	  return b._claripy.false

		# TODO: FIX: restore post-refactor
		#if (a.op == Simplifier.SIMPLE_OPS or b.op in Simplifier.SIMPLE_OPS) and a.length > 1 and a.length == b.length:
		#	for i in xrange(a.length):
		#		a_bit = a[i:i]
		#		if a_bit.symbolic:
		#			break
		#		b_bit = b[i:i]
		#		if b_bit.symbolic:
		#			break
		#		if a_bit != b_bit:
		#			return _true_structure

	def boolean_and_simplifier(self, expr):
		args = expr.args
		if len(args) == 1:
			return args[0]

		new_args = []
		for a in args:
			if a == _false_structure:
				return _false_structure
			elif a != _true_structure:
				new_args.append(a)

		if len(new_args) < len(args):
			return self._new_structure('And', new_args)

		def _flattening_filter(args):
			# a And a == a
			return tuple(OrderedSet(args))

		return self._flatten_simplifier(expr, _flattening_filter, *args)

	def boolean_or_simplifier(self, expr):
		args = expr.args
		if len(args) == 1:
			return args[0]

		new_args = []
		for a in args:
			if a  == _true_structure:
				return _true_structure
			elif a != _false_structure:
				new_args.append(a)

		if len(new_args) < len(args):
			return self._new_structure('Or', new_args)

		def _flattening_filter(args):
			# a Or a == a
			return tuple(OrderedSet(args))

		return self._flatten_simplifier(expr, _flattening_filter, *args)

	def boolean_not_simplifier(self, expr):
		body = expr.args[0]
		if body.op == '__eq__':
			return self._new_structure('__ne__', (body.args[0], body.args[1]))
		elif body.op == '__ne__':
			return self._new_structure('__eq__', (body.args[0], body.args[1]))

		if body.op == 'Not':
			return body.args[0]

		if body.op == 'If':
			return self._new_structure('If', (body.args[0], body.args[2], body.args[1]))

		if body.op == 'SLT':
			return self._new_structure('SGE', (body.args[0], body.args[1]))
		elif body.op == 'SLE':
			return self._new_structure('SGT', (body.args[0], body.args[1]))
		elif body.op == 'SGT':
			return self._new_structure('SLE', (body.args[0], body.args[1]))
		elif body.op == 'SGE':
			return self._new_structure('SLT', (body.args[0], body.args[1]))

		if body.op == 'ULT':
			return self._new_structure('UGE', (body.args[0], body.args[1]))
		elif body.op == 'ULE':
			return self._new_structure('UGT', (body.args[0], body.args[1]))
		elif body.op == 'UGT':
			return self._new_structure('ULE', (body.args[0], body.args[1]))
		elif body.op == 'UGE':
			return self._new_structure('ULT', (body.args[0], body.args[1]))

		if body.op == '__lt__':
			return self._new_structure('UGE', (body.args[0], body.args[1]))
		elif body.op == '__le__':
			return self._new_structure('UGT', (body.args[0], body.args[1]))
		elif body.op == '__gt__':
			return self._new_structure('ULE', (body.args[0], body.args[1]))
		elif body.op == '__ge__':
			return self._new_structure('ULT', (body.args[0], body.args[1]))

	#
	# oh gods -- floating point simplifiers
	#

	@staticmethod
	def fptobv_simplifier(expr):
		the_fp = expr.args[0]
		if the_fp.op == 'fpToFP' and len(the_fp.args) == 2:
			return the_fp.args[0]

	@staticmethod
	def fptofp_simplifier(expr):
		args = expr.args
		if len(args) == 2 and args[0].op == 'fpToIEEEBV':
			to_bv, sort = args
			if sort == fp.FSORT_FLOAT and to_bv.length == 32:
				return to_bv.args[0]
			elif sort == fp.FSORT_DOUBLE and to_bv.length == 64:
				return to_bv.args[0]

simplifier = Simplifier()

from .utils import OrderedSet
#from . import ast
from . import fp
from . import operations
from .ast.structure import ASTStructure, get_structure, _true_structure, _false_structure
from .backend_manager import backends
