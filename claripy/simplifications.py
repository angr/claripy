import collections
import itertools
import operator

from functools import reduce
from .utils import OrderedSet


class SimplificationManager:
	def __init__(self):
		self._simplifiers = {
			'Reverse': self.boolean_reverse_simplifier,
			'And': self.boolean_and_simplifier,
			'Or': self.boolean_or_simplifier,
			'Not': self.boolean_not_simplifier,
			'Extract': self.extract_simplifier,
			'Concat': self.concat_simplifier,
			'If': self.if_simplifier,
			'__lshift__': self.lshift_simplifier,
			'__rshift__': self.rshift_simplifier,
			'__eq__': self.eq_simplifier,
			'__ne__': self.ne_simplifier,
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

	def simplify(self, op, args):
		if op not in self._simplifiers:
			return None
		return self._simplifiers[op](*args)

	#
	# The simplifiers.
	#

	#pylint:disable=inconsistent-return-statements

	@staticmethod
	def if_simplifier(cond, if_true, if_false):
		if cond.is_true():
			return if_true

		if cond.is_false():
			return if_false

	@staticmethod
	def concat_simplifier(*args):

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
					concatted = ast.all_operations.Concat(previous, current)
					# If the concrete arguments to concat have non-relocatable annotations attached,
					# we may not be able to simplify the concrete concat. This check makes sure we don't
					# create a nested concat in that case.
					#
					# This is necessary to ensure that simplified is set correctly. If we don't check this here,
					# later the concat-of-concat will eliminate the newly introduced concat again, meaning we end
					# up with the same args that we started with. But because we only eliminate the concat later,
					# the simplified variable would still be set to True after this loop which is wrong.
					if concatted.op != "Concat":
						args[i-1:i+1] = (concatted,)
						continue

				i += 1

			if len(args) < len(orig_args):
				simplified = True

		# here, we flatten any concats among the arguments and remove zero-length arguments
		i = 0
		while i < len(args):
			current = args[i]
			if current.length == 0:
				args.pop(i)
				simplified = True
			elif current.op == 'Concat':
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
			elif prev_var is args[i].args[2] and prev_right == args[i].args[0] + 1:
				prev_right = args[i].args[1]
				args[i-1:i+1] = [ ast.all_operations.Extract(prev_left, prev_right, prev_var) ]
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
			return ast.all_operations.Concat(*args)

		return

	@staticmethod
	def rshift_simplifier(val, shift):
		if (shift == 0).is_true():
			return val

	@staticmethod
	def lshift_simplifier(val, shift):
		if (shift == 0).is_true():
			return val

	@staticmethod
	def eq_simplifier(a, b):
		if a is b:
			return ast.true

		if isinstance(a, ast.Bool) and b is ast.true:
			return a
		if isinstance(b, ast.Bool) and a is ast.true:
			return b
		if isinstance(a, ast.Bool) and b is ast.false:
			return ast.all_operations.Not(a)
		if isinstance(b, ast.Bool) and a is ast.false:
			return ast.all_operations.Not(b)

		if a.op == 'Reverse' and b.op == 'Reverse':
			return a.args[0] == b.args[0]

		# TODO: all these ==/!= might really slow things down...
		if a.op == 'If':
			if a.args[1] is b and ast.all_operations.is_true(a.args[2] != b):
				# (If(c, x, y) == x, x != y) -> c
				return a.args[0]
			elif a.args[2] is b and ast.all_operations.is_true(a.args[1] != b):
				# (If(c, x, y) == y, x != y) -> !c
				return ast.all_operations.Not(a.args[0])
			# elif a._claripy.is_true(a.args[1] == b) and a._claripy.is_true(a.args[2] == b):
			#	  return a._claripy.true
			# elif a._claripy.is_true(a.args[1] != b) and a._claripy.is_true(a.args[2] != b):
			#	  return a._claripy.false

		if b.op == 'If':
			if b.args[1] is a and ast.all_operations.is_true(b.args[2] != b):
				# (x == If(c, x, y)) -> c
				return b.args[0]
			elif b.args[2] is a and ast.all_operations.is_true(b.args[1] != a):
				# (y == If(c, x, y)) -> !c
				return ast.all_operations.Not(b.args[0])
			# elif b._claripy.is_true(b.args[1] == a) and b._claripy.is_true(b.args[2] == a):
			#	  return b._claripy.true
			# elif b._claripy.is_true(b.args[1] != a) and b._claripy.is_true(b.args[2] != a):
			#	  return b._claripy.false

		if (a.op in SIMPLE_OPS or b.op in SIMPLE_OPS) and a.length > 1 and a.length == b.length:
			for i in range(a.length):
				a_bit = a[i:i]
				if a_bit.symbolic:
					break

				b_bit = b[i:i]
				if b_bit.symbolic:
					break

				if ast.all_operations.is_false(a_bit == b_bit):
					return ast.all_operations.false

	@staticmethod
	def ne_simplifier(a, b):
		if a is b:
			return ast.false

		if a.op == 'Reverse' and b.op == 'Reverse':
			return a.args[0] != b.args[0]

		if a.op == 'If':
			if a.args[2] is b and ast.all_operations.is_true(a.args[1] != b):
				# (If(c, x, y) == x, x != y) -> c
				return a.args[0]
			elif a.args[1] is b and ast.all_operations.is_true(a.args[2] != b):
				# (If(c, x, y) == y, x != y) -> !c
				return ast.all_operations.Not(a.args[0])
			# elif a._claripy.is_true(a.args[1] == b) and a._claripy.is_true(a.args[2] == b):
			#	  return a._claripy.false
			# elif a._claripy.is_true(a.args[1] != b) and a._claripy.is_true(a.args[2] != b):
			#	  return a._claripy.true

		if b.op == 'If':
			if b.args[2] is a and ast.all_operations.is_true(b.args[1] != a):
				# (x == If(c, x, y)) -> c
				return b.args[0]
			elif b.args[1] is a and ast.all_operations.is_true(b.args[2] != a):
				# (y == If(c, x, y)) -> !c
				return ast.all_operations.Not(b.args[0])
			# elif b._claripy.is_true(b.args[1] != a) and b._claripy.is_true(b.args[2] != a):
			#	  return b._claripy.true
			# elif b._claripy.is_true(b.args[1] == a) and b._claripy.is_true(b.args[2] == a):
			#	  return b._claripy.false

		if (a.op == SIMPLE_OPS or b.op in SIMPLE_OPS) and a.length > 1 and a.length == b.length:
			for i in range(a.length):
				a_bit = a[i:i]
				if a_bit.symbolic:
					break

				b_bit = b[i:i]
				if b_bit.symbolic:
					break

				if ast.all_operations.is_true(a_bit != b_bit):
					return ast.all_operations.true

	@staticmethod
	def boolean_reverse_simplifier(body):
		if body.op == 'Reverse':
			return body.args[0]

		if body.length == 8:
			return body

		if body.op == 'Concat':
			if all(a.op == 'Extract' for a in body.args):
				first_ast = body.args[0].args[2]
				for i,a in enumerate(body.args):
					if not (first_ast is a.args[2]
							and a.args[0] == ((i + 1) * 8 - 1)
							and a.args[1] == i * 8):
						break
				else:
					upper_bound = body.args[-1].args[0]
					if first_ast.length == upper_bound + 1:
						return first_ast
					else:
						return first_ast[upper_bound:0]
			if all(a.length == 8 for a in body.args):
				return body.make_like(body.op, body.args[::-1])

		if body.op == 'Concat':
			if all(a.op == 'Reverse' for a in body.args):
				if all(a.length % 8 == 0 for a in body.args):
					return body.make_like(body.op,reversed([a.args[0] for a in body.args]))

	@staticmethod
	def boolean_and_simplifier(*args):
		if len(args) == 1:
			return args[0]

		new_args = []
		for a in args:
			if a.is_false():
				return ast.all_operations.false
			elif not a.is_true():
				new_args.append(a)

		if not new_args:
			return ast.bool.true

		if len(new_args) < len(args):
			return ast.all_operations.And(*new_args)

		def _flattening_filter(args):
			# a And a == a
			return tuple(OrderedSet(args))

		flattened = SimplificationManager._flatten_simplifier('And', _flattening_filter, *args)
		fargs = flattened.args if flattened is not None else args

		# Check if we are left with one argument again
		if len(fargs) == 1:
			return fargs[0]

		if any(len(arg.args) != 2 for arg in fargs):
			return flattened

		target_var = None

		# Determine the unknown variable
		if fargs[0].args[0].symbolic:
			if fargs[0].args[0] is fargs[1].args[0]:
				target_var = fargs[0].args[0]
			elif fargs[0].args[0] is fargs[1].args[1]:
				target_var = fargs[0].args[0]
		elif fargs[0].args[1].symbolic:
			if fargs[0].args[1] is fargs[1].args[0]:
				target_var = fargs[0].args[1]
			elif fargs[0].args[1] is fargs[1].args[1]:
				target_var = fargs[0].args[1]

		if target_var is None:
			return flattened

		# we now know that the And is a series of binary conditions over a single variable.
		# we can optimize accordingly.
		# right now it's just check for eq/ne

		eq_list = []
		ne_list = []
		for arg in fargs:
			other = arg.args[1] if arg.args[0] is target_var else arg.args[0]
			if arg.op == '__eq__':
				eq_list.append(other)
			elif arg.op == '__ne__':
				ne_list.append(other)
			else:
				return flattened

		if not eq_list:
			return flattened
		if any(any(ne is eq for eq in eq_list) for ne in ne_list):
			return ast.all_operations.false
		if all(v.op == 'BVV' for v in eq_list) and all(v.op == 'BVV' for v in ne_list):
			mustbe = eq_list[0]
			if any(eq.args[0] != mustbe.args[0] for eq in eq_list):
				return ast.all_operations.false
			return target_var == eq_list[0]
		return flattened

	@staticmethod
	def boolean_or_simplifier(*args):
		if len(args) == 1:
			return args[0]

		new_args = []
		for a in args:
			if a.is_true():
				return ast.all_operations.true
			elif not a.is_false():
				new_args.append(a)

		if len(new_args) < len(args):
			return ast.all_operations.Or(*new_args)

		def _flattening_filter(args):
			# a Or a == a
			return tuple(OrderedSet(args))

		return SimplificationManager._flatten_simplifier('Or', _flattening_filter, *args)

	@staticmethod
	def _flatten_simplifier(op_name, filter_func, *args, **kwargs):
		if not any(isinstance(a, ast.Base) and a.op == op_name for a in args):
			return

		# we cannot further flatten if any top-level argument has non-relocatable annotaitons
		if any(not anno.relocatable for anno in itertools.chain.from_iterable(arg.annotations for arg in args)):
			return

		new_args = tuple(itertools.chain.from_iterable(
			(a.args if isinstance(a, ast.Base) and a.op == op_name else (a,)) for a in args
		))
		if filter_func: new_args = filter_func(new_args)
		if not new_args and 'initial_value' in kwargs:
			return kwargs['initial_value']
		return next(a for a in args if isinstance(a, ast.Base)).make_like(op_name, new_args)

	@staticmethod
	def bitwise_add_simplifier(a, b):
		if a is ast.all_operations.BVV(0, a.size()):
			return b
		elif b is ast.all_operations.BVV(0, a.size()):
			return a

		return SimplificationManager._flatten_simplifier('__add__', None, a, b)

	@staticmethod
	def bitwise_mul_simplifier(a, b):
		return SimplificationManager._flatten_simplifier('__mul__', None, a, b)

	@staticmethod
	def bitwise_sub_simplifier(a, b):
		if b is ast.all_operations.BVV(0, a.size()):
			return a
		elif a is b or (a == b).is_true():
			return ast.all_operations.BVV(0, a.size())

	# recognize b-bit z=signedmax(q,r) from this idiom:
	# s=q-r;t=q^r;u=s^q;v=u&t;w=v^s;x=rshift(w,b-1);y=x&t;z=q^y
	# and recognize b-bit z=signedmin(q,r) from this idiom:
	# s=r-q;t=q^r;u=s^r;v=u&t;w=v^s;x=rshift(w,b-1);y=x&t;z=q^y
	@staticmethod
	def bitwise_xor_simplifier_minmax(a,b):
		q,y = a,b
		if y.op != '__and__':
			q,y = b,a
			if y.op != '__and__': return

		if len(y.args) != 2: return
		x,t = y.args
		if t.op != '__xor__':
			t,x = y.args
			if t.op != '__xor__': return

		if x.op != '__rshift__': return
		w,dist = x.args

		bits = a.size()
		if dist is not ast.all_operations.BVV(bits - 1,bits): return
		if w.op != '__xor__': return

		if len(w.args) != 2: return
		v,s = w.args
		if s.op != '__sub__':
			s,v = w.args
			if s.op != '__sub__': return

		if v.op != '__and__': return
		if len(v.args) != 2: return
		u,t2 = v.args
		if t2 is not t:
			t2,u = v.args
			if t2 is not t: return

		if u.op != '__xor__': return

		if len(t.args) != 2: return
		q2,r = t.args
		if q2 is not q:
			r,q2 = t.args
			if q2 is not q: return

		if (u.args[0] is s and u.args[1] is q) or (u.args[0] is q and u.args[1] is s):
			if not (s.args[0] is q and s.args[1] is r): return
			cond = ast.all_operations.SLE(q,r)
			return ast.all_operations.If(cond,r,q)

		if (u.args[0] is s and u.args[1] is r) or (u.args[0] is r and u.args[1] is s):
			if not (s.args[0] is r and s.args[1] is q): return
			cond = ast.all_operations.SLE(q,r)
			return ast.all_operations.If(cond,q,r)

	@staticmethod
	def bitwise_xor_simplifier(a, b):
		if a is ast.all_operations.BVV(0, a.size()):
			return b
		elif b is ast.all_operations.BVV(0, a.size()):
			return a
		elif a is b or (a == b).is_true():
			return ast.all_operations.BVV(0, a.size())

		result = SimplificationManager.bitwise_xor_simplifier_minmax(a,b)
		if result is not None: return result

		def _flattening_filter(args):
			# since a ^ a == 0, we can safely remove those from args
			# this procedure is done carefully in order to keep the ordering of arguments
			ctr = collections.Counter(args)
			unique_args = set(k for k in ctr if ctr[k] % 2 != 0)
			return tuple([ arg for arg in args if arg in unique_args ])

		return SimplificationManager._flatten_simplifier('__xor__', _flattening_filter, a, b, initial_value=ast.all_operations.BVV(0, a.size()))

	@staticmethod
	def bitwise_or_simplifier(a, b):
		if a is ast.all_operations.BVV(0, a.size()):
			return b
		elif b is ast.all_operations.BVV(0, a.size()):
			return a
		elif (a == b).is_true():
			return a
		elif a is b:
			return a

		def _flattening_filter(args):
			# a | a == a
			return tuple(OrderedSet(args))

		return SimplificationManager._flatten_simplifier('__or__', _flattening_filter, a, b)

	@staticmethod
	def bitwise_and_simplifier(a, b):
		if (a == 2**a.size()-1).is_true():
			return b
		elif (b == 2**a.size()-1).is_true():
			return a
		elif (a == b).is_true():
			return a
		elif a is b:
			return a

		def _flattening_filter(args):
			# a & a == a
			return tuple(OrderedSet(args))

		return SimplificationManager._flatten_simplifier('__and__', _flattening_filter, a, b)

	@staticmethod
	def boolean_not_simplifier(body):
		if body.op == '__eq__':
			return body.args[0] != body.args[1]
		elif body.op == '__ne__':
			return body.args[0] == body.args[1]

		if body.op == 'Not':
			return body.args[0]

		if body.op == 'If':
			return ast.all_operations.If(body.args[0], body.args[2], body.args[1])

		if body.op == 'SLT':
			return ast.all_operations.SGE(body.args[0], body.args[1])
		elif body.op == 'SLE':
			return ast.all_operations.SGT(body.args[0], body.args[1])
		elif body.op == 'SGT':
			return ast.all_operations.SLE(body.args[0], body.args[1])
		elif body.op == 'SGE':
			return ast.all_operations.SLT(body.args[0], body.args[1])

		if body.op == 'ULT':
			return ast.all_operations.UGE(body.args[0], body.args[1])
		elif body.op == 'ULE':
			return ast.all_operations.UGT(body.args[0], body.args[1])
		elif body.op == 'UGT':
			return ast.all_operations.ULE(body.args[0], body.args[1])
		elif body.op == 'UGE':
			return ast.all_operations.ULT(body.args[0], body.args[1])

		if body.op == '__lt__':
			return ast.all_operations.UGE(body.args[0], body.args[1])
		elif body.op == '__le__':
			return ast.all_operations.UGT(body.args[0], body.args[1])
		elif body.op == '__gt__':
			return ast.all_operations.ULE(body.args[0], body.args[1])
		elif body.op == '__ge__':
			return ast.all_operations.ULT(body.args[0], body.args[1])

	@staticmethod
	def zeroext_simplifier(n, e):
		if n == 0:
			return e

	@staticmethod
	def signext_simplifier(n, e):
		if n == 0:
			return e

		# TODO: if top bit is 0, do a zero-extend instead

	@staticmethod
	def extract_simplifier(high, low, val):
		# if we're extracting the whole value, return the value
		if high - low + 1 == val.size():
			return val

		if (val.op == 'SignExt' or val.op == 'ZeroExt') and low == 0 and high + 1 == val.args[1].size():
			return val.args[1]

		if val.op == 'ZeroExt':
			extending_bits = val.args[0]
			if extending_bits == 0:
				val = val.args[1]
			else:
				val = ast.all_operations.Concat(ast.all_operations.BVV(0, extending_bits), val.args[1])

		# Reverse(concat(a, b)) -> concat(Reverse(b), Reverse(a))
		# a and b must have lengths that are a multiple of 8
		if val.op == 'Reverse' and val.args[0].op == 'Concat' and all(a.length % 8 == 0 for a in val.args[0].args):
			val = ast.all_operations.Concat(*reversed([a.reversed for a in val.args[0].args]))

		# Reading one byte from a reversed ast can be converted to reading the corresponding byte from the original ast
		# No Reverse is required then
		if val.op == 'Reverse' and high - low + 1 == 8 and low % 8 == 0:
			byte_pos = low // 8
			new_byte_pos = val.length // 8 - byte_pos - 1

			val = val.args[0]
			high = (new_byte_pos + 1) * 8 - 1
			low = new_byte_pos * 8

			return ast.all_operations.Extract(high, low, val)

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
				self = used[0]
			else:
				self = ast.all_operations.Concat(*used)

			new_high = low_loc + high - low
			if new_high == self.length - 1 and low_loc == 0:
				return self
			else:
				if self.op != 'Concat':
					return self[new_high:low_loc]
				else:
					# to avoid infinite recursion we only return if something was simplified
					if len(used) != len(val.args) or new_high != high or low_loc != low:
						return ast.all_operations.Extract(new_high, low_loc, self)

		if val.op == 'Extract':
			_, inner_low = val.args[:2]
			new_low = inner_low + low
			new_high = new_low + (high - low)
			return (val.args[2])[new_high:new_low]

		if val.op == 'Reverse' and val.args[0].op == 'Concat' and all(a.length % 8 == 0 for a in val.args[0].args):
			val = val.make_like('Concat',
								tuple(reversed([a.reversed for a in val.args[0].args])),
			)[high:low]
			if not val.symbolic:
				return val

		# if all else fails, convert Extract(Reverse(...)) to Reverse(Extract(...))
		# if val.op == 'Reverse' and (high + 1) % 8 == 0 and low % 8 == 0:
		#	  print("saw reverse, converting")
		#	  inner_length = val.args[0].length
		#	  try:
		#		  return val.args[0][(inner_length - 1 - low):(inner_length - 1 - low - (high - low))].reversed
		#	  except ClaripyOperationError:
		#		  __import__('ipdb').set_trace()

		if val.op in extract_distributable:
			all_args = tuple(a[high:low] for a in val.args)
			return reduce(getattr(operator, val.op), all_args)

	# oh gods
	@staticmethod
	def fptobv_simplifier(the_fp):
		if the_fp.op == 'fpToFP' and len(the_fp.args) == 2:
			return the_fp.args[0]

	@staticmethod
	def fptofp_simplifier(*args):
		if len(args) == 2 and args[0].op == 'fpToIEEEBV':
			to_bv, sort = args
			if sort == fp.FSORT_FLOAT and to_bv.length == 32:
				return to_bv.args[0]
			elif sort == fp.FSORT_DOUBLE and to_bv.length == 64:
				return to_bv.args[0]

SIMPLE_OPS = ('Concat', 'SignExt', 'ZeroExt')

extract_distributable = {
	'__and__', '__rand__',
	'__or__', '__ror__',
	'__xor__', '__rxor__',
}

from .backend_manager import backends
from . import ast
from . import fp


# the actual instance
simpleton = SimplificationManager()
