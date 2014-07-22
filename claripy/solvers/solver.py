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
		self._simplified = True
		self.constraints = [ ]
		self._timeout = timeout if timeout is not None else 300000

	def _independent_constraints(self, constraints=None):
		'''
		Returns independent constraints, split from this Solver's constraints.
		'''

		sets_list = [ ]
		for i in self.constraints if constraints is None else constraints:
			sets_list.extend(i.split(['And']))

		l.debug("... sets_list: %r", sets_list)

		set_sets = { }
		for s in sets_list:
			l.debug("... processing %r with variables %r", s, s.variables)
			c = [ s ]
			vv = set(s.variables)

			for v in s.variables:
				if v in set_sets:
					for sv in set_sets[v]:
						vv.update(sv.variables)
					c.extend(set_sets[v])

			if len(vv) == 0:
				vv = { "CONSTANT" }

			for v in vv:
				l.debug("...... setting %s to %r", v, c)
				set_sets[v] = c

		l.debug("... set_sets: %r", set_sets)

		results = [ ]
		seen_lists = set()
		for c_list in set_sets.values():
			if id(c_list) in seen_lists:
				continue

			seen_lists.add(id(c_list))
			variables = set()
			for c in c_list:
				variables |= c.variables
			l.debug("... appending variables %r with constraints %r", variables, c_list)
			results.append((variables, c_list))

		return results


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

		#if n == 1 and extra_constraints is None:
		#	self.check()
		#	return [ e.eval(backends=[self._results_backend], model=self._result.model) ]

		return [ self._results_backend.convert(i, model=self._result.model) for i in self._eval(e, n, extra_constraints=extra_constraints) ]

	def max(self, e, extra_constraints=None):
		if self._result is None and self.check() != sat:
			raise UnsatError('unsat')

		if not e.symbolic:
			return [ e.eval(backends=[self._results_backend]) ]
		return self._results_backend.convert(self._max(e, extra_constraints=extra_constraints), model=self._result.model)

	def min(self, e, extra_constraints=None):
		if self._result is None and self.check() != sat:
			raise UnsatError('unsat')

		if not e.symbolic:
			return [ e.eval(backends=[self._results_backend]) ]
		return self._results_backend.convert(self._min(e, extra_constraints=extra_constraints), model=self._result.model)

	def _eval(self, e, n, extra_constraints=None):
		raise NotImplementedError()
	def _max(self, e, extra_constraints=None):
		raise NotImplementedError()
	def _min(self, e, extra_constraints=None):
		raise NotImplementedError()

	def solution(self, e, v):
		try:
			n = self.any(e, extra_constraints=[e==v])
			if n != v:
				raise Exception("wtf")

			return True
		except UnsatError:
			return False

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
