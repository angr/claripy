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

	def solve(self):
		raise NotImplementedError()

	def satisfiable(self):
		return self.solve()

	def any(self, expr, extra_constraints=None):
		return self.eval(expr, 1, extra_constraints)[0]

	def eval(self, e, n, extra_constraints=None):
		if type(e) is not E: raise ValueError("Solver got a non-E for e.")
		if self._result is None and not self.satisfiable(): raise UnsatError('unsat')

		if not e.symbolic and extra_constraints is None:
			r = [ e.eval(backends=[self._results_backend]) ]
		elif not e.symbolic and extra_constraints is not None:
			if not self._solver_backend.check(extra_constraints=extra_constraints):
				raise UnsatError('unsat')
			r = [ self._results_backend.convert_expr(e) ]
		else:
			o = self._solver_backend.convert_expr(e)
			r = [ self._results_backend.convert(i, model=self._result.model) for i in self._eval(o, n, extra_constraints=extra_constraints) ]
		return [ self._results_backend.wrap(i) for i in r ]

	def max(self, e, extra_constraints=None):
		self.simplify()

		two = self.eval(e, 2, extra_constraints=extra_constraints)
		if len(two) == 1: return two[0]

		o = self._solver_backend.convert_expr(e)
		c = ([ ] if extra_constraints is None else extra_constraints) + [ self._claripy.UGE(e, two[0]) ]
		r = self._results_backend.convert(self._max(o, extra_constraints=c), model=self._result.model)
		return self._results_backend.wrap(r)

	def min(self, e, extra_constraints=None):
		self.simplify()

		two = self.eval(e, 2, extra_constraints=extra_constraints)
		if len(two) == 1: return two[0]

		o = self._solver_backend.convert_expr(e)
		c = ([ ] if extra_constraints is None else extra_constraints) + [ self._claripy.ULE(e, two[0]) ]
		r = self._results_backend.convert(self._min(o, extra_constraints=c), model=self._result.model)
		return self._results_backend.wrap(r)

	def _eval(self, e, n, extra_constraints=None):
		raise NotImplementedError()
	def _max(self, e, extra_constraints=None):
		raise NotImplementedError()
	def _min(self, e, extra_constraints=None):
		raise NotImplementedError()

	def solution(self, e, v):
		raise NotImplementedError()
		return self._solver_backend.check(extra_constraints=[e==v])

	def eval_value(self, e, n, extra_constraints=None):
		return [ self._results_backend.primitive_expr(r) for r in self.eval(e, n, extra_constraints=extra_constraints) ]
	def min_value(self, e, extra_constraints=None):
		return self._results_backend.primitive_expr(self.min(e, extra_constraints=extra_constraints))
	def max_value(self, e, extra_constraints=None):
		return self._results_backend.primitive_expr(self.max(e, extra_constraints=extra_constraints))
	def any_value(self, expr, extra_constraints=None):
		return self._results_backend.primitive_expr(self.eval(expr, 1, extra_constraints)[0])

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
		merged = self.__class__(self._claripy, solver_backend=self._solver_backend, results_backend=self._results_backend, timeout=self._timeout)
		options = [ ]

		for s, v in zip([self]+others, merge_values):
			options.append(self._solver_backend.call('And', [ merge_flag == v ] + s.constraints))
		merged.add(self._solver_backend.call('Or', options))
		return merged

	def combine(self, others):
		combined = self.__class__(self._claripy, solver_backend=self._solver_backend, results_backend=self._results_backend, timeout=self._timeout)

		combined.add(*self.constraints)
		for o in others:
			combined.add(*o.constraints)
		return combined

	def split(self):
		results = [ ]
		l.debug("Splitting!")
		for variables,c_list in self._independent_constraints():
			l.debug("... got %d constraints with variables %r", len(c_list), variables)

			s = self.__class__(self._claripy, self._solver_backend, self._results_backend, timeout=self._timeout)
			s.add(*c_list)
			results.append(s)
		return results

from ..result import UnsatError
from ..expression import E
