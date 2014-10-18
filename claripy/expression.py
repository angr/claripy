#!/usr/bin/env python

import collections
import weakref
import logging
l = logging.getLogger("claripy.expression")

import ana

class E(ana.Storable):
	'''
	A class to wrap expressions.
	'''
	__slots__ = [ '_claripy', 'variables', 'symbolic', '_model', '_objects', '_simplified', '_errored_backends' ]
	_hash_cache = weakref.WeakValueDictionary()

	def __new__(cls, claripy, model, variables, symbolic, **kwargs):
		h = hash(model)
		if h in cls._hash_cache:
			return cls._hash_cache[h]
		else:
			self = super(E, cls).__new__(cls, claripy, model, variables, symbolic, **kwargs)
			cls._hash_cache[h] = self
			return self

	def __init__(self, claripy, model, variables, symbolic, objects=None, simplified=False, errored_backends=None):
		if hasattr(self, '_model'):
			# already been initialized, and the stupid __new__ call is calling it again...
			return

		if variables is None or symbolic is None or model is None:
			raise ClaripyExpressionError("invalid arguments passed to E()")

		self._claripy = claripy
		self._objects = { }
		self._simplified = simplified
		self._errored_backends = set() if errored_backends is None else errored_backends

		self.variables = variables
		self.symbolic = symbolic
		self._model = model

		if objects is not None:
			self._objects.update(objects)

	@property
	def uuid(self):
		return self.ana_uuid

	#
	# Model and AST
	#

	@property
	def model(self):
		for b in self._claripy.model_backends:
			try: return self.model_for(b)
			except BackendError: self._errored_backends.add(b)
		return self._model

	@property
	def ast(self):
		return self._model

	def model_for(self, b, result=None):
		if b in self._errored_backends and result is None:
			raise BackendError("backend %s has already errored out" % b)

		if b in self._objects:
			return self._objects[b]
		elif not isinstance(self._model, A):
			return b.convert(self._model, result=result)

		resolved=False
		for o in self._objects.itervalues():
			try:
				r = b.convert(o, result=result)
				resolved = True
			except BackendError:
				pass

		if not resolved:
			r = self._model.resolve(b, result=result)

		if result is None:
			self._objects[b] = r

		return r

	#
	# Some debug stuff:
	#

	@staticmethod
	def _part_count(a):
		return sum([ E._part_count(aa) for aa in a.args ]) if isinstance(a, A) else E._part_count(a._model) if isinstance(a, E) else 1

	@staticmethod
	def _depth(a):
		return max([ E._depth(aa)+1 for aa in a.args ]) if isinstance(a, A) else E._depth(a._model) if isinstance(a, E) else 1

	@staticmethod
	def _hash_counts(a, d=None):
		if d is None: d = collections.defaultdict(int)
		d[(a.__class__, hash(a))] += 1

		if isinstance(a, A):
			for aa in a.args:
				E._hash_counts(aa, d=d)
		elif isinstance(a, E):
			E._hash_counts(a._model, d=d)
		return d

	def __hash__(self):
		return hash(self._model)

	def __nonzero__(self):
		raise ClaripyExpressionError('testing Expressions for truthiness does not do what you want, as these expressions can be symbolic')

	def __repr__(self):
		start = "E"
		if self.symbolic:
			start += "S"

		start += "("
		end = ")"

		return start + str(self.model) + end

	def split(self, split_on):
		if not isinstance(self._model, A):
			return [ self ]

		if self._model.op in split_on:
			l.debug("Trying to split: %r", self._model)
			if all(isinstance(a, E) for a in self._model.args):
				return self._model.args[:]
			else:
				raise ClaripyExpressionError('the abstraction of this expression was not done with "%s" in split_on' % self._model.op)
		else:
			l.debug("no split for you")
			return [ self ]

	#
	# Storing and loading of expressions
	#

	def _ana_getstate(self):
		return self._claripy.name, self._model, self.variables, self.symbolic, self._simplified

	def _ana_setstate(self, s):
		cn, model, variables, symbolic, simplified = s
		self.__init__(Claripies[cn], model, variables, symbolic, simplified=simplified)

	#
	# BV operations
	#

	def __len__(self):
		if type(self._model) is A:
			return self._model.size()
		else:
			for b in self._claripy.model_backends:
				try: return b.call_expr('size', (self,))
				except BackendError: pass
			raise ClaripyExpressionError("unable to determine size of expression")
	size = __len__

	@property
	def length(self):
		return self.size()

	def __iter__(self):
		raise ClaripyExpressionError("Please don't iterate over Expressions!")

	def chop(self, bits=1):
		s = len(self)
		if s % bits != 0:
			raise ValueError("expression length (%d) should be a multiple of 'bits' (%d)" % (len(self), bits))
		elif s == bits:
			return [ self ]
		else:
			return list(reversed([ self[(n+1)*bits - 1:n*bits] for n in range(0, s / bits) ]))

	def reversed(self, lazy=True):
		'''
		Reverses the expression.
		'''
		return self._claripy.Reverse(self, lazy=lazy)
	reverse = reversed

	def __getitem__(self, rng):
		if type(rng) is slice:
			return self._claripy.Extract(int(rng.start), int(rng.stop), self)
		else:
			return self._claripy.Extract(int(rng), int(rng), self)

	def zero_extend(self, n):
		return self._claripy.ZeroExt(n, self)

	def sign_extend(self, n):
		return self._claripy.SignExt(n, self)

	def _replace(self, old, new):
		# this means that we can't possible contain the desired expression
		if not self.variables >= old.variables:
			return self, False

		if hash(self) == hash(old):
			return new, True
		elif not isinstance(self.ast, A):
			return self, False
		else:
			new_ast, replaced = self.ast._replace(old, new)
			if replaced:
				vars = new_ast.variables | new.variables
				return E(self._claripy, new_ast, vars, new_ast.symbolic), True
			else:
				return self, False

	def replace(self, old, new):
		if not isinstance(old, E) or not isinstance(new, E):
			raise ClaripyExpressionError('replacements must be expressions')

		if old.size() != new.size():
			raise ClaripyExpressionError('replacements must have matching sizes')

		return self._replace(old, new)[0]

#
# Wrap stuff
#

def e_operator(cls, op_name):
	def wrapper(self, *args):
		return self._claripy._do_op(op_name, (self,) + tuple(args))
	wrapper.__name__ = op_name
	setattr(cls, op_name, wrapper)

def make_methods():
	for name in expression_operations:
		e_operator(E, name)

from .errors import ClaripyExpressionError, BackendError
from .operations import expression_operations
make_methods()
from .ast import A
from . import Claripies
