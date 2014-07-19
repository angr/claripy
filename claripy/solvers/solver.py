#!/usr/bin/env python

import logging
l = logging.getLogger("claripy.solvers.solver")

class Solver(object):
	def __init__(self, claripy, solver_backend=None, results_backend=None, timeout=None):
		self._claripy = claripy
		self._solver_backend = solver_backend if solver_backend is not None else claripy.solver_backend
		self._results_backend = results_backend if results_backend is not None else claripy.results_backend

		self._finalized = None
		self._result = None
		self._variables = None
		self._simplified = True
		self._timeout = timeout if timeout is not None else 300000

	#
	# Constraints
	#

	def add(self, *constraints, **kwargs):
		raise NotImplementedError()

	#
	# Solving
	#

	def check(self):
		raise NotImplementedError()

	def satisfiable(self):
		return self.check() == sat

	def any(self, expr, extra_constraints=None):
		return self.eval(expr, 1, extra_constraints)[0]

	def eval(self, e, n, extra_constraints=None):
		if self._result is None and self.check() != sat:
			raise UnsatError('unsat')

		if not e.symbolic:
			return [ e.eval(backends=[self._results_backend]) ]

		if n == 1 and extra_constraints is None:
			self.check()
			return [ e.eval(backends=[self._results_backend], model=self._result.model) ]

		return self._eval(e, n, extra_constraints=extra_constraints)

	def max(self, e, extra_constraints=None):
		if self._result is None and self.check() != sat:
			raise UnsatError('unsat')

		if not e.symbolic:
			return [ e.eval(backends=[self._results_backend]) ]
		return self._max(e, extra_constraints=extra_constraints)

	def min(self, e, extra_constraints=None):
		if self._result is None and self.check() != sat:
			raise UnsatError('unsat')

		if not e.symbolic:
			return [ e.eval(backends=[self._results_backend]) ]
		return self._min(e, extra_constraints=extra_constraints)

	def _eval(self, e, n, extra_constraints=None):
		raise NotImplementedError()
	def _max(self, e, extra_constraints=None):
		raise NotImplementedError()
	def _min(self, e, extra_constraints=None):
		raise NotImplementedError()

	#
	# Merging and splitting
	#

	def finalize(self):
		raise NotImplementedError()

	def simplify(self):
		raise NotImplementedError()

	def branch(self):
		raise NotImplementedError()

	def merge(self, others, merge_flag, merge_values):
		raise NotImplementedError()

	def combine(self, others):
		raise NotImplementedError()

	def split(self):
		raise NotImplementedError()

from ..result import sat, UnsatError
