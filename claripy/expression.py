#!/usr/bin/env python

import collections
import logging
l = logging.getLogger("claripy.expression")

from .storable import Storable

class E(Storable):
	'''
	A class to wrap expressions.
	'''
	__slots__ = [ 'variables', 'symbolic', '_uuid', '_model', '_stored', '_objects', '_simplified', '__weakref__', '_pending_operations' ]

	def __init__(self, claripy, variables=None, symbolic=None, uuid=None, objects=None, model=None, stored=False, simplified=False):
		Storable.__init__(self, claripy, uuid=uuid)
		have_uuid = uuid is not None
		have_data = not (variables is None or symbolic is None or model is None)
		self._objects = { }
		self._simplified = simplified

		if have_uuid and not have_data:
			self._load()
		elif have_data:
			self.variables = variables
			self.symbolic = symbolic

			self._uuid = uuid
			self._model = model
			self._stored = stored

			if objects is not None:
				self._objects.update(objects)
		else:
			raise ValueError("invalid arguments passed to E()")

	#
	# Model and AST
	#

	@property
	def model(self):
		for b in self._claripy.model_backends:
			try: return self.model_for(b)
			except BackendError: pass
		return self._model

	@property
	def ast(self):
		return self._model

	def model_for(self, b, result=None, save=None):
		if b in self._objects:
			return self._objects[b]
		elif not isinstance(self._model, A):
			return b.convert(self._model, result=result)

		save = save if save is not None else result is None

		resolved=False
		for o in self._objects.itervalues():
			try:
				r = b.convert(o, result=result)
				resolved = True
			except BackendError:
				pass

		if not resolved:
			r = self._model.resolve(b, save=save, result=result)

		if save:
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

	def _load(self):
		e = self._claripy.datalayer.load_expression(self._uuid)
		self.variables = e.variables
		self.symbolic = e.symbolic

		self._uuid = e._uuid
		self._model = e._model
		self._stored = e._stored

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

	def store(self):
		self._claripy.datalayer.store_expression(self)

	def __getstate__(self):
		if self._uuid is not None:
			l.debug("uuid pickle on %s", self)
			return self._uuid
		l.debug("full pickle on %s", self)
		return self._uuid, self._model, self.variables, self.symbolic, self._simplified

	def __setstate__(self, s):
		if type(s) is str:
			self.__init__(get_claripy(), uuid=s)
			return

		uuid, model, variables, symbolic, simplified = s
		self.__init__(get_claripy(), variables=variables, symbolic=symbolic, model=model, uuid=uuid, simplified=simplified)

	def copy(self):
		c = E(claripy=self._claripy, variables=self.variables, symbolic=self.symbolic, uuid=self._uuid, objects=self._objects, model=self._model, stored=self._stored, simplified=self._simplified)
		return c

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
from . import get_claripy
from .ast import A
