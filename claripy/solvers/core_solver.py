#!/usr/bin/env python

# pylint: disable=F0401

import time
import logging

l = logging.getLogger("claripy.solvers.core_solver")

# we need to:
#  receive constraints
#  make a hash of the constraints
#  check for existing solution in the solution cache
#  solve

from .solver import Solver

import itertools
symbolic_count = itertools.count()

class CoreSolver(Solver):
	def __init__(self, claripy, solver_backend=None, results_backend=None, timeout=None, solver=None):
		Solver.__init__(self, claripy, timeout=timeout, solver_backend=solver_backend, results_backend=results_backend)

		self._solver = self._create_solver() if solver is None else solver

		self._result = None
		self.variables = set()

	#
	# Util stuff
	#

	def _create_solver(self):
		solver = self._solver_backend.solver()
		solver.set('timeout', self._timeout)
		return solver

	#
	# Constraints
	#

	def add(self, *constraints):
		if len(constraints) == 0:
			return None

		if type(constraints[0]) in (list, tuple):
			raise Exception("don't pass lists to Solver.add()!")

		self._result = None

		self.constraints += constraints
		for e in constraints:
			self.variables.update(e.variables)

		self._solver_backend.add_exprs(self._solver, constraints)
		self._simplified = False

	#
	# Solving
	#

	def solve(self):
		if self._result is not None:
			return self._result.sat

		# check it!
		l.debug("Checking SATness of %d constraints", len(self.constraints))
		a = time.time()
		self._result = self._solver_backend.results(self._solver)
		b = time.time()
		l.debug("... %s in %s seconds", self._result.sat, b - a)

		return self._result.sat

	def _eval(self, e, n, extra_constraints=None):
		return self._solver_backend.eval(self._solver, e, n, extra_constraints=extra_constraints, model=self._result.backend_model)
	def _max(self, e, extra_constraints=None):
		return self._solver_backend.max(self._solver, e, extra_constraints=extra_constraints, model=self._result.backend_model)
	def _min(self, e, extra_constraints=None):
		return self._solver_backend.min(self._solver, e, extra_constraints=extra_constraints, model=self._result.backend_model)

	def solution(self, e, v):
		return self._solver_backend.check(self._solver, extra_constraints=[self._solver_backend.convert_expr(e==v)])

	#
	# Merging/splitting
	#

	def simplify(self):
		if self._simplified:
			return

		converted = [ self._solver_backend.convert_expr(c) for c in self.constraints ]
		self.constraints = [ self._solver_backend.simplify_expr(self._solver_backend.call('And', converted)) ]
		self._solver = self._create_solver()
		self._solver_backend.add_exprs(self._solver, self.constraints)
		self._simplified = True

	def branch(self):
		raise Exception("CoreSolver can't branch, yo!")
	def finalize(self):
		raise Exception("CoreSolver can't finalize, yo!")
