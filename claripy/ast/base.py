import sys
import logging
import weakref
import itertools

l = logging.getLogger("claripy.ast")

#pylint:enable=unused-argument
#pylint:disable=unidiomatic-typecheck


#
# Deduplication and caching
#

class ASTCacheKey(object):
	def __init__(self, a):
		self.ast = a

	def __hash__(self):
		return hash(self.ast)

	def __eq__(self, other):
		return hash(self.ast) == hash(other.ast)

	def __repr__(self):
		return '<Key %s %s>' % (self.ast._type_name(), self.ast.__repr__(inner=True))

def _concrete_evaluate(expr):
	if not expr._eager:
		return expr

	try:
		return backends.concrete._abstract(backends.concrete.convert(expr))
	except BackendError:
		expr._eager = False

	return expr

def _simplify(expr):
	return expr.swap_structure(simplifier.simplify(expr.structure))

_default_symbolic_filters = ( _simplify, )
_default_concrete_filters = ( _concrete_evaluate, )

_hash_cache = weakref.WeakValueDictionary()
def _deduplicate(expr):
	return _hash_cache.setdefault(hash(expr), expr)

#
# AST variable naming
#

var_counter = itertools.count()
_unique_names = True

def _make_name(name, size, explicit_name=False, prefix=""):
	if _unique_names and not explicit_name:
		return "%s%s_%d_%d" % (prefix, name, var_counter.next(), size)
	else:
		return name

class Base(object):
	"""
	An AST tracks a tree of operations on arguments. It has the following methods:
	"""

	__slots__ = [
		'structure', 'outer_annotations', 'filters',
		'cache_key', '_hash', '_eager',
		'_simplified', '_excavated', '_burrowed',
		'outer_annotations'
	]

	def __init__(self, structure, outer_annotations, filters=None, _eager=True):
		"""
		This is called when you create a new Base object, whether directly or through an operation.
		It finalizes the arguments (see the _finalize function, above) and then computes
		a hash. If an AST of this hash already exists, it returns that AST. Otherwise,
		it creates, initializes, and returns the AST.

		:param structure:			The structure of the AST (operation, arguments, etc).
		:param outer_annotations:	A frozenset of annotations applied onto this AST.
		:param filters:				Filter functions to run on this AST after every operation.
		:param eager_backends:		A list of backends with which to attempt eager evaluation
		"""

		# store the AST structure
		self.structure = structure

		# whether this AST could be eager evaluated
		self._eager = _eager

		# the list of annotations applied to the outer level of the AST
		self.outer_annotations = outer_annotations

		# these are filters that get applied to the AST at every operation
		self.filters = () if filters is None else filters

		# a cache key, to use when storing this AST in dicts (to survive bucket collisions)
		self.cache_key = ASTCacheKey(self)

		# references to various transformations of this AST
		self._excavated = None
		self._burrowed = None
		self._simplified = None

		# the hash
		self._hash = None

	def _deduplicate(self):
		return _deduplicate(self)

	@property
	def uc_alloc_depth(self):
		"""
		The depth of allocation by lazy-initialization. It's only used in under-constrained symbolic execution mode.
		"""
		raise Exception("TODO")

	@property
	def uninitialized(self):
		"""
		Whether this AST comes from an uninitialized dereference or not. It's only used in under-constrained symbolic
		execution mode.
		"""
		raise Exception("TODO")

	@property
	def op(self):
		"""
		The operation of the AST.
		"""
		return self.structure.op

	@property
	def args(self):
		"""
		The arguments of the AST.
		"""
		return self.structure.args

	@property
	def inline_annotations(self):
		"""
		The inline annotations on the AST.
		"""
		return self.structure.annotations

	@property
	def ite_burrowed(self):
		"""
		Returns an equivalent AST that "burrows" the ITE expressions as deep as possible into the ast, for simpler
		printing.
		"""
		return self.swap_structure(self.structure._burrow_ite())

	@property
	def ite_excavated(self):
		"""
		Returns an equivalent AST that "excavates" the ITE expressions out as far as possible toward the root of the
		AST, for processing in static analyses.
		"""
		return self.swap_structure(self.structure._excavate_ite())

	@property
	def variables(self):
		raise Exception("TODO")

	@property
	def symbolic(self):
		try:
			return backends.symbolic.convert(self)
		except BackendError:
			return None

	@property
	def length(self):
		try:
			return backends.length.convert(self)
		except BackendError:
			return None

	def _apply_filters(self):
		new_ast = self
		for f in new_ast.filters:
			try:
				l.debug("Running filter %s.", f)
				new_ast = f(new_ast) if hasattr(f, '__call__') else f.convert(new_ast)
			except BackendError:
				l.warning("Ignoring BackendError during AST filter application.")
		return new_ast

	def __hash__(self):
		if self._hash is None:
			self._hash = self._calc_hash()
		return self._hash

	def _calc_hash(self):
		"""
		Calculates the hash of an AST.

		"""
		return hash((self.structure, self.outer_annotations, self.filters))

	#
	# AST modifications.
	#

	def swap_args(self, new_args):
		"""
		This returns the same AST, with the arguments swapped out for new_args.
		"""

		return self.swap_structure(self.structure.swap_args(new_args))

	def swap_structure(self, structure):
		"""
		This returns the same AST, with the structure swapped out for a different one.
		"""

		a = self.__class__(structure, self.outer_annotations, filters=self.filters)
		return a._apply_filters()

	def swap_inline_annotations(self, new_tuple):
		"""
		Replaces annotations on this AST.

		:param new_tuple: the tuple of annotations to replace the old annotations with
		:returns: a new AST, with the annotations added
		"""
		return self.swap_structure(self.structure.swap_annotations(new_tuple))

	def swap_outer_annotations(self, new_tuple):
		"""
		Replaces annotations on this AST.

		:param new_tuple: the tuple of annotations to replace the old annotations with
		:returns: a new AST, with the annotations added
		"""
		return self.__class__(self.structure, new_tuple, filters=self.filters, _eager=self._eager)

	#def replace(self, old, new):
	#	"""
	#	Returns an AST with all instances of the AST 'old' replaced with AST 'new'.
	#	"""
	#	replacements = {old.structure: new.structure}
	#	return self.swap_structure(self.structure.replace(replacements))

	#
	# Annotations
	#

	def annotate_inline(self, *args):
		"""
		Appends annotations to this AST.

		:param args: the tuple of annotations to append (variadic positional args)
		:returns: a new AST, with the annotations added
		"""
		return self.swap_structure(self.structure.annotate(*args))

	def annotate_outer(self, *args):
		"""
		Appends annotations to this AST.

		:param args: the tuple of annotations to append (variadic positional args)
		:returns: a new AST, with the annotations added
		"""
		return self.swap_outer_annotations(self.outer_annotations + args)

	#
	# Viewing and debugging
	#

	def dbg_repr(self, prefix=None):
		try:
			if prefix is not None:
				new_prefix = prefix + "    "
				s = prefix + "<%s %s (\n" % (type(self).__name__, self.op)
				for a in self.args:
					s += "%s,\n" % (a.dbg_repr(prefix=new_prefix) if hasattr(a, 'dbg_repr') else (new_prefix + repr(a)))
				s = s[:-2] + '\n'
				s += prefix + ")>"

				return s
			else:
				return "<%s %s (%s)>" % (type(self).__name__, self.op, ', '.join(a.dbg_repr() if hasattr(a, 'dbg_repr') else repr(a) for a in self.args))
		except RuntimeError:
			e_type, value, traceback = sys.exc_info()
			raise ClaripyRecursionError, ("Recursion limit reached during display. I sorry.", e_type, value), traceback

	def shallow_repr(self, max_depth=8):
		return self.__repr__(max_depth=max_depth)

	def __repr__(self, **kwargs):
		return "<%s%s %s>" % (self.__class__.__name__, str(self.length) if self.length is not None else '', self.structure.repr(**kwargs))

	#
	# Other helper functions
	#

	def split(self, split_on):
		"""
		Splits the AST if its operation is `split_on` (i.e., return all the arguments). Otherwise, return a list with
		just the AST.
		"""
		if self.op in split_on: return list(self.args)
		else: return [ self ]

	# we don't support iterating over Base objects
	def __iter__(self):
		"""
		This prevents people from iterating over ASTs.
		"""
		raise ClaripyOperationError("Please don't iterate over, or split, AST nodes!")

	def __nonzero__(self):
		"""
		This prevents people from accidentally using an AST as a condition. For
		example, the following was previously a common error:

			a,b = two ASTs
			if a == b:
				do something

		The problem is that `a == b` would return an AST, because an AST can be symbolic
		and there could be no way to actually know the value of that without a
		constraint solve. This caused tons of issues.
		"""
		raise ClaripyOperationError('testing Expressions for truthiness does not do what you want, as these expressions can be symbolic')

	#
	# these are convenience operations
	#

	def _first_backend(self, what):
		for b in backends._all_backends:
			#if b in self._errored:
			#	continue

			try: return getattr(b, what)(self)
			except BackendError: pass

	@property
	def singlevalued(self):
		return self._first_backend('singlevalued')

	@property
	def multivalued(self):
		return self._first_backend('multivalued')

	@property
	def cardinality(self):
		return self._first_backend('cardinality')

	@property
	def concrete(self):
		return backends.concrete.handles(self)

	#
	# Backwards compatibility crap
	#

	#def __getattr__(self, a):
	#	if not a.startswith('_model_'):
	#		raise AttributeError(a)

	#	model_name = a[7:]
	#	if not hasattr(backends, model_name):
	#		raise AttributeError(a)

	#	try:
	#		return getattr(backends, model_name).convert(self)
	#	except BackendError:
	#		return self

#
# Simplification helper
#

def simplify(e):
	if isinstance(e, Base) and e.op == 'I':
		return e

	s = e._first_backend('simplify')
	if s is None:
		l.debug("Unable to simplify expression")
		return e
	else:
		return s

#
# Operation support
#

def make_op(name, arg_types, return_type, do_coerce=True, bound=True): #pylint:disable=unused-argument
	if type(arg_types) in (tuple, list): #pylint:disable=unidiomatic-typecheck
		expected_num_args = len(arg_types)
	elif type(arg_types) is type: #pylint:disable=unidiomatic-typecheck
		expected_num_args = None
	else:
		raise ClaripyOperationError("op {} got weird arg_types".format(name))

	def _type_fixer(args):
		num_args = len(args)
		if expected_num_args is not None and num_args != expected_num_args:
			raise ClaripyTypeError(
				"Operation {} takes exactly {} arguments ({} given)".format(name, len(arg_types), len(args))
			)

		if type(arg_types) is type: #pylint:disable=unidiomatic-typecheck
			actual_arg_types = (arg_types,) * num_args
		else:
			actual_arg_types = arg_types
		matches = [ isinstance(arg, argty) for arg,argty in zip(args, actual_arg_types) ]

		# heuristically, this works!
		thing = args[matches.index(True)] if True in matches else None

		for arg, argty, matches in zip(args, actual_arg_types, matches):
			if not matches:
				if do_coerce and hasattr(argty, '_from_' + type(arg).__name__):
					convert = getattr(argty, '_from_' + type(arg).__name__)
					yield convert(thing, arg).structure
				else:
					yield NotImplemented
					return
			else:
				yield arg.structure if isinstance(arg, Base) else arg

	def _op(*args):
		fixed_args = tuple(_type_fixer(args))
		if any(i is NotImplemented for i in fixed_args):
			return NotImplemented
		ast_args = [ a for a in args if isinstance(a, Base) ]

		new_structure = ASTStructure(name, fixed_args, ())
		new_outer_annotations = frozenset().union(*(a.outer_annotations for a in ast_args))
		new_eager = all(a._eager for a in ast_args)
		nondefault_filters = [ a.filters for a in ast_args if a.filters is not _default_symbolic_filters and a.filters is not _default_concrete_filters ]
		if nondefault_filters:
			new_filters = max(nondefault_filters, key=len)
		elif any(a.filters is _default_symbolic_filters for a in ast_args):
			new_filters = _default_symbolic_filters
		else:
			new_filters = _default_concrete_filters

		return return_type(new_structure, new_outer_annotations, filters=new_filters, _eager=new_eager)._apply_filters()._deduplicate()

	return _op

def make_reversed_op(op_func):
	def _reversed_op(*args):
		return op_func(*args[::-1])
	return _reversed_op

from ..errors import BackendError, ClaripyOperationError, ClaripyRecursionError, ClaripyTypeError
from ..backend_manager import backends
from ..simplifier import simplifier
from .structure import ASTStructure
