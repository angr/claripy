#!/usr/bin/env python

# pylint: disable=F0401

import time
import logging

l = logging.getLogger("claripy.solvers.standalone_solver")

# we need to:
#  receive constraints
#  make a hash of the constraints
#  check for existing solution in the solution cache
#  solve

from .solver import Solver

import itertools
symbolic_count = itertools.count()

class CoreSolver(Solver):
	def __init__(self, claripy, solver_backend=None, results_backend=None, timeout=None):
		Solver.__init__(self, claripy)

		self._timeout = timeout if timeout is not None else 300000
		self._solver_backend = solver_backend if solver_backend is not None else claripy.solver_backend
		self._results_backend = results_backend if results_backend is not None else claripy.results_backend

		self._solver = None
		self._create_solver()

		self._result = None
		self.constraints = [ ]
		self.variables = set()

	#
	# Util stuff
	#

	def _create_solver(self):
		self._solver = self._solver_backend.solver()
		self._solver.set('timeout', self._timeout)

	#
	# Constraints
	#

	def add(self, *constraints):
		if len(constraints) == 0:
			return None

		self._result = None

		self.constraints += constraints
		for e in constraints:
			self.variables.update(e.variables)
			e_raw = e.eval(backends=[self._solver_backend])
			l.debug("adding %r", e_raw)
			self._solver.add(e_raw)

		self._simplified = False

	#
	# Solving
	#

	def check(self):
		if self._result is not None:
			return self._result

		# check it!
		l.debug("Checking SATness of %d constraints", len(self.constraints))
		a = time.time()
		self._result = self._solver_backend.solve(self._solver)
		b = time.time()
		l.debug("... %s in %s seconds", self._result.sat, b - a)

		return self._result.sat

	def eval(self, e, n, extra_constraints=None):
		if not e.symbolic:
			return [ e.eval(backends=[self._results_backend]) ]

		if n == 1 and extra_constraints is None:
			self.check()
			return [ e.eval(backends=[self._results_backend], model=self._result.model) ]
		else:
			return self._solver_backend.eval(self._solver, e, n, extra_constraints=extra_constraints)

	def max(self, e, extra_constraints=None):
		return self._solver_backend.max(e, extra_constraints=None)
	def min(self, e, extra_constraints=None):
		return self._solver_backend.min(e, extra_constraints=None)


	#
	# Merging/splitting
	#

	def simplify(self):
		if self._simplified:
			return

		self.constraints = [ self._solver_backend.simplify(self._solver_backend.call('And', self.constraints)) ]
		self._simplified = True

	def merge(self, others, merge_flag, merge_values):
		merged = self._solver_backend.solver()
		options = [ ]

		for s, v in zip([self]+others, merge_values):
			options.append(self._solver_backend.call('And', [[ merge_flag == v ] + s.constraints]))
		merged.add_constraints(*options)
		return merged

	def combine(self, others):
		combined = self._solver_backend.solver()

		combined.add(*self.constraints)
		for o in others:
			combined.add(*o.constraints)
		return combined

	def _independent_constraints(self):
		'''
		Returns independent constraints, split from this Solver's constraints.
		'''

		sets_list = [ ]
		for i in self.constraints:
			sets_list.extend(i.split(['And']))

		l.debug("... sets_list: %r", sets_list)

		set_sets = { }
		for s in sets_list:
			l.debug("... processing %r with variables %r", s, s.variables)
			c = [ s ]
			for v in s.variables:
				if v in set_sets:
					c.extend(set_sets[v])
			for v in s.variables:
				set_sets[v] = c

		l.debug("... set_sets: %r", set_sets)

		results = [ ]
		for c_list in set_sets.values():
			variables = set()
			for c in c_list:
				variables |= c.variables
			results.append((variables, c_list))

		return results

	def split(self):
		results = [ ]
		l.debug("Splitting!")
		for variables,c_list in self._independent_constraints():
			l.debug("... got %d constraints with variables %r", len(c_list), variables)

			s = self.__class__(self._claripy, self._solver_backend, self._results_backend, timeout=self._timeout)
			s.add(*c_list)
			results.append(s)
		return results

	def branch(self):
		raise Exception("CoreSolver can't branch, yo!")
	def finalize(self):
		raise Exception("CoreSolver can't finalize, yo!")
