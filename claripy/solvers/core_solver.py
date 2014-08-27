#!/usr/bin/env python

# pylint: disable=F0401

import time
import logging

l = logging.getLogger("claripy.solvers.core_solver")
l_timing = logging.getLogger("claripy.solvers.core_solver_timing")

# we need to:
#  receive constraints
#  make a hash of the constraints
#  check for existing solution in the solution cache
#  solve

from .solver import Solver

import itertools
symbolic_count = itertools.count()

class CoreSolver(Solver):
	def __init__(self, claripy, solver_backend=None, results_backend=None, timeout=None, solver=None, result=None):
		Solver.__init__(self, claripy, timeout=timeout, solver_backend=solver_backend, results_backend=results_backend, result=result)

		self._to_add = [ ]
		self.constraints = [ ]
		self._solver = solver
		self.variables = set()

	def downsize(self):
		self._solver = None

	def _get_solver(self):
		if self._solver is None:
			self._solver = self._create_solver()
			self._solver_backend.add_exprs(self._solver, self.constraints)
		elif len(self._to_add) > 0:
			self._solver_backend.add_exprs(self._solver, self._to_add)
			self._to_add = [ ]

		return self._solver

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
		l.debug("%s.add(*%s)", self, constraints)

		if len(constraints) == 0:
			return None

		if type(constraints[0]) in (list, tuple):
			raise ValueError("don't pass lists to Solver.add()!")

		to_add = [ ]
		for e in constraints:
			#e_simp = self._solver_backend.simplify_expr(e)
			e_simp = e
			if not e_simp.symbolic and self._results_backend.convert_expr(e_simp):
				continue
			elif not e_simp.symbolic and not self._results_backend.convert_expr(e_simp):
				self._result = Result(False, { })
				f = self._claripy.BoolVal(False)
				self.constraints.append(f)
				self._to_add.append(f)
				return

			self._result = None
			self._simplified = False
			self.constraints.append(e_simp)
			to_add.append(e_simp)
			self.variables.update(e_simp.variables)

		if self._solver is not None:
			self._to_add += to_add
			#self._solver_backend.add_exprs(self._solver, to_add)

	#
	# Solving
	#

	def _solve(self, extra_constraints=None):
		l.debug("%s.solve(extra_constraints=%s)", self, extra_constraints)

		# check it!
		l_timing.debug("Checking SATness of %d constraints", len(self.constraints))
		a = time.time()
		r = self._solver_backend.results(self._get_solver(), extra_constraints=self._solver_backend.convert_exprs(extra_constraints) if extra_constraints is not None else None, results_backend=self._results_backend)
		b = time.time()
		l_timing.debug("... %s in %s seconds", r.sat, b - a)
		return r


	def _eval(self, e, n, extra_constraints=None):
		l.debug("%s._eval(%s, %s, extra_constraints=%s)", self, e, n, extra_constraints)

		if n > 1:
			return self._solver_backend.eval(self._get_solver(), e, n, extra_constraints=extra_constraints, model=self._result.backend_model, results_backend=self._results_backend)

		try:
			return self._results_backend.eval(None, e, n, extra_constraints=extra_constraints, model=self._result.model)
		except BackendError:
			return self._solver_backend.eval(self._get_solver(), e, n, extra_constraints=extra_constraints, model=self._result.backend_model, results_backend=self._results_backend)

	def _max(self, e, extra_constraints=None):
		l.debug("%s._max(%s, extra_constraints=%s)", self, e, extra_constraints)

		try:
			return self._results_backend.max(None, e, extra_constraints=extra_constraints, model=self._result.model)
		except BackendError:
			return self._solver_backend.max(self._get_solver(), e, extra_constraints=extra_constraints, model=self._result.backend_model)

	def _min(self, e, extra_constraints=None):
		l.debug("%s._min(%s, extra_constraints=%s)", self, e, extra_constraints)

		try:
			return self._results_backend.min(None, e, extra_constraints=extra_constraints, model=self._result.model)
		except BackendError:
			return self._solver_backend.min(self._get_solver(), e, extra_constraints=extra_constraints, model=self._result.backend_model)

	def _solution(self, e, v):
		try:
			a = self._results_backend.eval(None, self._results_backend.convert_expr(e), 1, model=self._result.model)[0]
			print a
			b = self._results_backend.convert(v)
			print b
			return a == b
		except BackendError:
			return self._solver_backend.check(self._get_solver(), extra_constraints=[self._solver_backend.convert_expr(e==v)])

	#
	# Merging/splitting
	#

	def simplify(self):
		if self._simplified:
			return

		if len(self.constraints) == 0:
			return

		converted = [ self._solver_backend.convert_expr(c) for c in self.constraints ]

		if len(converted) == 0:
			self.constraints = [ ]
		else:
			self.constraints = [ self._solver_backend.simplify_expr(self._solver_backend.call('And', converted)) ]

		self._solver = None
		self._simplified = True

	def branch(self):
		raise Exception("CoreSolver can't branch, yo!")
	def finalize(self):
		raise Exception("CoreSolver can't finalize, yo!")

from ..result import Result
from ..backends.backend import BackendError
