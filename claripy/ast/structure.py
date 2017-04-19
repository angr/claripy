import itertools
import logging
import weakref
import hashlib
import cPickle as pickle
import struct
import sys
import ana

_md5_unpacker = struct.Struct('2Q')
l = logging.getLogger("claripy.expressions.structure")

#
# Some helpers
#

def _inner_repr(a, **kwargs):
	if isinstance(a, ASTStructure):
		return a.repr(inner=True, **kwargs)
	else:
		return repr(a)

#
# AST Structure
#

class ASTStructure(ana.Storable):
	def __init__(self, op, args, annotations=()):
		self.op = op
		self.args = args
		self.annotations = annotations
		self._hash = None

	def __hash__(self):
		if self._hash is None:
			self._hash = self._calc_hash()
		return self._hash

	def _calc_hash(self):
		"""
		Calculates the hash of an ASTStructure, given the operation, args, and kwargs.

		:param op:		The operation.
		:param args:	The arguments to the operation.
		:param kwargs:	A dict including the 'symbolic', 'variables', and 'length' items.

		:returns:		a hash.

		"""
		args_tup = tuple(long(a) if type(a) is int else (a if type(a) in (long, float) else hash(a)) for a in self.args)
		to_hash = (self.op, args_tup, hash(self.annotations))

		# Why do we use md5 when it's broken? Because speed is more important
		# than cryptographic integrity here. Then again, look at all those
		# allocations we're doing here... fast python is painful.
		hd = hashlib.md5(pickle.dumps(to_hash, -1)).digest()
		return _md5_unpacker.unpack(hd)[0] # 64 bits

	def __eq__(self, o):
		return self is o or hash(self) == hash(o) or (self.op == o.op and self.args == o.args and self.annotations == o.annotations)

	@property
	def symbolic(self):
		return backends.symbolic.convert(self)
	@property
	def length(self):
		return backends.length.convert(self)

	#
	# Various structural modifications
	#

	def annotate(self, *annotations):
		return _deduplicate(ASTStructure(self.op, self.args, self.annotations+annotations))

	def swap_annotations(self, annotations):
		return _deduplicate(ASTStructure(self.op, self.args, annotations))

	def swap_args(self, args):
		if len(self.args) == len(args) and all(a is b for a,b in zip(self.args, args)):
			return self
		return _deduplicate(ASTStructure(self.op, args, self.annotations))

	def replace(self, replacements, leaf_operation=None):
		"""
		A helper for replace().

		:param replacements: A dictionary of hashes to their replacements.
		"""
		try: return replacements[self]
		except KeyError: pass

		if leaf_operation is not None and self.op in operations.leaf_operations:
			r = leaf_operation(self)
		else:
			new_args = [
				a._replace(replacements=replacements, leaf_operation=leaf_operation) if isinstance(a, ASTStructure) else a
				for a in self.args
			]

			if any(old_a is not new_a for old_a,new_a in zip(self.args,new_args)):
				r = self.swap_args(tuple(new_args))
			else:
				r = self

		replacements[self] = r
		return r

	def canonicalize(self, var_map=None, counter=None):
		"""
		Converts the structure to a canonical form (just normalizing variable names for now).

		:param var_map:	A map of variable name normalizations -- MODIFIED IN PLACE.
		:param counter: An iterator to generate normalized numbers for names.

		:returns: a tuple of (new_var_map, new_counter, new_structure)
		"""

		counter = itertools.count() if counter is None else counter
		var_map = { } if var_map is None else var_map

		for v in self._recursive_leaves():
			if v.cache_key not in var_map and v.op in { 'BVS', 'BoolS', 'FPS' }:
				new_name = 'cv%d' % next(counter)
				var_map[v.cache_key] = v.swap_args((new_name,)+v.args)

		return var_map, counter, self.replace(var_map)

	#
	# Serialization support
	#

	def _ana_getstate(self):
		"""
		Support for ANA serialization.
		"""
		return self.op, self.args, self.annotations, hash(self)

	def _ana_setstate(self, state):
		"""
		Support for ANA deserialization.
		"""
		self.op, self.args, self.annotations, self._hash = state
		_hash_cache[self._hash] = self

	def make_uuid(self, uuid=None):
		"""
		This overrides the default ANA uuid with the hash of the AST. UUID is slow, and we'll soon replace it from ANA
		itself, and this will go away.

		:returns: a string representation of the AST hash.
		"""
		u = getattr(self, '_ana_uuid', None)
		if u is None:
			u = str(hash(self)) if uuid is None else uuid
			ana.get_dl().uuid_cache[u] = self
			setattr(self, '_ana_uuid', u)
		return u

	#
	# Debugging
	#

	@property
	def dbg_recursive_children(self):
		for a in self.args:
			if isinstance(a, ASTStructure):
				l.debug("Yielding node %s with hash %s with %d children", a, hash(a), len(a.args))
				yield a
				for b in a.recursive_children:
					yield b

	@property
	def dbg_recursive_leaves(self):
		return self._recursive_leaves()

	def _recursive_leaves(self, seen=None):
		leaf = all(not isinstance(a, ASTStructure) for a in self.args)
		if leaf:
			yield self
			return

		seen = set() if seen is None else seen
		for a in self.args:
			if isinstance(a, ASTStructure) and not a in seen:
				seen.add(a)
				for b in a._recursive_leaves(seen=seen):
					yield b

	def dbg_is_looped(self, seen=None, checked=None):
		seen = set() if seen is None else seen
		checked = set() if checked is None else checked

		l.debug("Checking node with hash %s for looping", hash(self))
		if self in seen:
			return self
		elif self in checked:
			return False
		else:
			seen.add(self)

			for a in self.args:
				if not isinstance(a, ASTStructure):
					continue

				r = a.dbg_is_looped(seen=set(seen), checked=checked)
				if r is not False:
					return r

			checked.add(self)
			return False

	@property
	def dbg_depth(self):
		"""
		The depth of this AST. For example, an AST representing (a+(b+c)) would have a depth of 2.
		"""
		return self._dbg_depth()

	def _dbg_depth(self, memoized=None):
		"""
		:param memoized:	A dict of ast hashes to depths we've seen before
		:return:			The depth of the AST. For example, an AST representing (a+(b+c)) would have a depth of 2.
		"""
		if memoized is None:
			memoized = dict()

		try: return memoized[self]
		except KeyError: pass

		try:
			return 1 + max(a._dbg_depth(memoized=memoized) for a in self.args if isinstance(a, ASTStructure))
		except TypeError:
			return 0

	#
	# String representation
	#

	def repr(self, inner=False, max_depth=None, explicit_length=False):
		if max_depth is not None and max_depth <= 0:
			return '...'

		if max_depth is not None:
			max_depth -= 1

		try:
			if self.op in operations.reversed_ops:
				op = operations.reversed_ops[self.op]
				args = self.args[::-1]
			else:
				op = self.op
				args = self.args

			if op == 'BVS' and inner:
				value = args[0]
			elif op == 'BVS':
				value = "%s" % args[0]
				extras = [ ]
				if args[1] is not None:
					extras.append("min=%s" % args[1])
				if args[2] is not None:
					extras.append("max=%s" % args[2])
				if args[3] is not None:
					extras.append("stride=%s" % args[3])
				if args[4] is True:
					extras.append("UNINITIALIZED")
				if len(extras) != 0:
					value += "{" + ", ".join(extras) + "}"
			elif op == 'BoolV':
				value = str(args[0])
			elif op == 'BVV':
				if self.args[0] is None:
					value = '!'
				elif self.args[1] < 10:
					value = format(self.args[0], '')
				else:
					value = format(self.args[0], '#x')
				value += ('#' + str(backends.length.convert(self))) if explicit_length else ''
			elif op == 'If':
				value = 'if {} then {} else {}'.format(_inner_repr(args[0], max_depth=max_depth),
													   _inner_repr(args[1], max_depth=max_depth),
													   _inner_repr(args[2], max_depth=max_depth))
				if inner:
					value = '({})'.format(value)
			elif op == 'Not':
				value = '!{}'.format(_inner_repr(args[0], max_depth=max_depth))
			elif op == 'Extract':
				value = '{}[{}:{}]'.format(_inner_repr(args[2], max_depth=max_depth), args[0], args[1])
			elif op == 'ZeroExt':
				value = '0#{} .. {}'.format(args[0], _inner_repr(args[1], max_depth=max_depth))
				if inner:
					value = '({})'.format(value)
			elif op == 'Concat':
				value = ' .. '.join(_inner_repr(a, explicit_length=True, max_depth=max_depth) for a in self.args)
			elif len(args) == 2 and op in operations.infix:
				value = '{} {} {}'.format(_inner_repr(args[0], max_depth=max_depth),
										  operations.infix[op],
										  _inner_repr(args[1], max_depth=max_depth))
				if inner:
					value = '({})'.format(value)
			else:
				value = "{}({})".format(op,
										', '.join(_inner_repr(a, max_depth=max_depth) for a in args))

			return value
		except RuntimeError:
			e_type, value, traceback = sys.exc_info()
			raise ClaripyRecursionError, ("Recursion limit reached during display. I sorry.", e_type, value), traceback

	#
	# This code handles burrowing ITEs deeper into the ast and excavating
	# them to shallower levels.
	#

	def _burrow_ite(self):
		if self.op != 'If':
			#print "i'm not an if"
			return self.swap_args(tuple((a._burrow_ite() if isinstance(a, ASTStructure) else a) for a in self.args))

		if not all(isinstance(a, ASTStructure) for a in self.args):
			#print "not all my args are bases"
			return self

		old_true = self.args[1]
		old_false = self.args[2]

		if old_true.op != old_false.op or len(old_true.args) != len(old_false.args):
			return self

		if old_true.op == 'If':
			# let's no go into this right now
			return self

		if any(a.op in operations.leaf_operations for a in self.args):
			# burrowing through these is pretty funny
			return self

		matches = [ old_true.args[i] == old_false.args[i] for i in range(len(old_true.args)) ]
		if matches.count(False) != 1 or all(matches):
			# TODO: handle multiple differences for multi-arg ast nodes
			#print "wrong number of matches:",matches,old_true,old_false
			return self

		different_idx = matches.index(False)
		inner_if = self.swap_args((self.args[0], old_true.args[different_idx], old_false.args[different_idx]))
		new_args = list(old_true.args)
		new_args[different_idx] = inner_if._burrow_ite()
		#print "replaced the",different_idx,"arg:",new_args
		return old_true.swap_args(new_args)

	def _excavate_ite(self):
		if self.op in operations.leaf_operations:
			return self

		excavated_args = [ (a._excavate_ite() if isinstance(a, ASTStructure) else a) for a in self.args ]
		ite_args = [ isinstance(a, ASTStructure) and a.op == 'If' for a in excavated_args ]

		if self.op == 'If':
			# if we are an If, call the If handler so that we can take advantage of its simplifiers
			# TODO: make this simplifiable
			return If(*excavated_args)
		elif ite_args.count(True) == 0:
			# if there are no ifs that came to the surface, there's nothing more to do
			return self.swap_args(excavated_args)
		else:
			# this gets called when we're *not* in an If, but there are Ifs in the args.
			# it pulls those Ifs out to the surface.
			cond = excavated_args[ite_args.index(True)].args[0]
			new_true_args = [ ]
			new_false_args = [ ]

			for a in excavated_args:
				#print "OC", cond.dbg_repr()
				#print "NC", Not(cond).dbg_repr()

				if not isinstance(a, ASTStructure) or a.op != 'If':
					new_true_args.append(a)
					new_false_args.append(a)
				elif a.args[0] is cond:
					#print "AC", a.args[0].dbg_repr()
					new_true_args.append(a.args[1])
					new_false_args.append(a.args[2])
				elif a.args[0] is Not(cond):
					#print "AN", a.args[0].dbg_repr()
					new_true_args.append(a.args[2])
					new_false_args.append(a.args[1])
				else:
					#print "AB", a.args[0].dbg_repr()
					# weird conditions -- giving up!
					return self.swap_args(excavated_args)

			return If(cond, self.swap_args(new_true_args), self.swap_args(new_false_args))

	def _deduplicate(self):
		return _deduplicate(self)


_hash_cache = weakref.WeakValueDictionary()
def _deduplicate(expr):
	return _hash_cache.setdefault(hash(expr), expr)

def _do_op(op, args):
	return _deduplicate(ASTStructure(op, args, ()))

from .. import operations
from ..errors import ClaripyRecursionError
from .bool import Not, If
from ..backend_manager import backends
