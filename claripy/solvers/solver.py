#!/usr/bin/env python

import logging
l = logging.getLogger("claripy.solvers.solver")

import time
l_timing = logging.getLogger("claripy.solvers.solver_timing")

cached_evals = 0
cached_min = 0
cached_max = 0
cached_solve = 0
filter_true = 0
filter_false = 0

from ..storable import Storable

class Solver(Storable):
	def __init__(self, claripy, result=None, timeout=None, solvers=None, to_add=None):
		Storable.__init__(self, claripy)
		self._finalized = None
		self._result = result
		self._simplified = True
		self._timeout = timeout if timeout is not None else 300000

		# solving
		self._solver_states = { } if solvers is None else solvers
		self._to_add = { } if to_add is None else to_add
		try:
			self.constraints = [ ]
			self.variables = set()
		except AttributeError:
			pass

	def _load(self):
		raise Exception('TODO')

	#
	# Solver Creation
	#

	def _get_solver(self, backend):
		if backend in self._solver_states:
			s = self._solver_states[backend]
			backend.add_exprs(s, self._to_add[backend])
			self._to_add[backend] = [ ]
		else:
			s = backend.solver(timeout=self._timeout)
			backend.add_exprs(s, self.constraints)
			self._solver_states[backend] = s
			self._to_add[backend] = [ ]

		return s

	#
	# Constraint management
	#

	def _independent_constraints(self, constraints=None):
		'''
		Returns independent constraints, split from this Solver's constraints.
		'''

		splitted = [ ]
		for i in self.constraints if constraints is None else constraints: #pylint:disable=E1101
			splitted.extend(i.split(['And']))

		l.debug("... splitted of size %d", len(splitted))

		variable_connections = { }
		constraint_connections = { }
		for n,s in enumerate(splitted):
			l.debug("... processing constraint with %d variables", len(s.variables))

			connected_variables = set(s.variables)
			connected_constraints = { n }

			if len(connected_variables) == 0:
				connected_variables.add('CONSTANT')

			for v in s.variables:
				if v in variable_connections:
					connected_variables |= variable_connections[v]
				if v in constraint_connections:
					connected_constraints |= constraint_connections[v]

			for v in connected_variables:
				variable_connections[v] = connected_variables
				constraint_connections[v] = connected_constraints

		unique_constraint_sets = set()
		for v in variable_connections:
			unique_constraint_sets.add((frozenset(variable_connections[v]), frozenset(constraint_connections[v])))

		results = [ ]
		for v,c_indexes in unique_constraint_sets:
			results.append((set(v), [ splitted[c] for c in c_indexes ]))
		return results

	def _constraint_filter(self, ec):
		global filter_true, filter_false

		fc = [ ]
		for e in ec if type(ec) in (list, tuple, set) else (ec,):
			#e_simp = self._claripy.simplify(e)
			e_simp = e
			for b in self._claripy.model_backends:
				try:
					o = b.convert_expr(e_simp)
					if o == False:
						filter_false += 1
						raise UnsatError("expressions contain False")
					elif o == True:
						filter_true +=1
						break
					else:
						l.warning("Solver._constraint_filter got non-boolean from model_backend")
						raise ClaripySolverError()
				except BackendError:
					pass
			else:
				fc.append(e_simp)

		return tuple(fc)

	def add(self, constraints, invalidate_cache=True):
		if type(constraints) not in (list, tuple):
			constraints = [ constraints ]

		if len(constraints) == 0:
			return None

		if type(constraints[0]) in (list, tuple):
			raise ValueError("don't pass lists to Solver.add()!")

		try:
			to_add = self._constraint_filter(constraints)
			if len(to_add) > 0 and invalidate_cache:
				self._result = None
		except UnsatError:
			to_add = [ self._claripy.false ]
			self._result = Result(False, { })

		if len(to_add) > 0:
			self._simplified = False
			self.constraints += to_add

			for e in to_add:
				self.variables.update(e.variables)

			for b in self._solver_states:
				self._to_add[b] += to_add

	def simplify(self):
		if self._simplified or len(self.constraints) == 0: return
		self.constraints = [ self._claripy.simplify(self._claripy.And(*self.constraints)) ]

		self._solver_states = { }
		self._to_add = { }
		self._simplified = True

	#
	# Solving
	#

	def solve(self, extra_constraints=()):
		global cached_solve
		try:
			extra_constraints = self._constraint_filter(extra_constraints)
		except UnsatError:
			return Result(False, { })

		if self._result is not None and not self._result.sat:
			return self._result

		if len(extra_constraints) == 0 and self._result is not None:
			cached_solve += 1
			return self._result
		else:
			r = self._solve(extra_constraints=extra_constraints)
			if r.sat or len(extra_constraints) == 0:
				self._result = r
			return r

	def satisfiable(self, extra_constraints=()):
		return self.solve(extra_constraints=extra_constraints).sat

	def any(self, expr, extra_constraints=()):
		v = self.eval(expr, 1, extra_constraints)
		if len(v) == 0:
			raise UnsatError("couldn't concretize any values")
		return v[0]

	def eval(self, e, n, extra_constraints=()):
		global cached_evals
		extra_constraints = self._constraint_filter(extra_constraints)

		if type(e) is not E: raise ValueError("Solver got a non-E for e.")

		if len(extra_constraints) == 0:
			for b in self._claripy.model_backends:
				try: return b.eval_expr(e, n, result=self._result)
				except BackendError: pass

		if not self.satisfiable(extra_constraints=extra_constraints): raise UnsatError('unsat')

		l.debug("Solver.eval() for UUID %s with n=%d and %d extra_constraints", e.uuid, n, len(extra_constraints))

		if len(extra_constraints) == 0 and e.uuid in self._result.eval_cache:
			cached_results = self._result.eval_cache[e.uuid][1]
			cached_n = self._result.eval_cache[e.uuid][0]

			if cached_n >= n or len(cached_results) < cached_n:
				cached_evals += min(len(cached_results), n)
				return list(cached_results)[:n]
			else:
				solver_extra_constraints = [ e != v for v in cached_results ]
		else:
			cached_results = set()
			cached_n = 0
			solver_extra_constraints = extra_constraints

		cached_evals += cached_n
		l.debug("... %d values (of %d) were already cached.", cached_n, n)

		# if we have a cache, cached_n < n and len(cached_results) == cached_n
		all_results = cached_results
		all_results |= set(self._eval(e, n-len(all_results), extra_constraints=solver_extra_constraints))
		l.debug("... got %d more values", len(all_results) - len(cached_results))

		if len(extra_constraints) == 0:
			l.debug("... adding cache of %d values for n=%d", len(all_results), n)
			self._result.eval_cache[e.uuid] = (n, all_results)
		else:
			# can't assume that we didn't knock out other possible solutions
			l.debug("... adding cache of %d values for n=%d", len(all_results), len(all_results))
			self._result.eval_cache[e.uuid] = (len(all_results), all_results)

		# if there are less possible solutions than n (i.e., meaning we got all the solutions for e),
		# add constraints to help the solver out later
		if len(extra_constraints) == 0 and len(all_results) < n:
			l.debug("... adding constraints for %d values for future speedup", len(all_results))
			self.add([self._claripy.Or(*[ e == v for v in all_results ])], invalidate_cache=False)

		return tuple(all_results)

	def max(self, e, extra_constraints=()):
		global cached_max
		extra_constraints = self._constraint_filter(extra_constraints)

		if len(extra_constraints) == 0:
			for b in self._claripy.model_backends:
				try: return b.max_expr(e, result=self._result)
				except BackendError: pass

		two = self.eval(e, 2, extra_constraints=extra_constraints)
		if len(two) == 0: raise UnsatError("unsat during max()")
		elif len(two) == 1: return two[0]

		if len(extra_constraints) == 0 and e.uuid in self._result.max_cache:
			cached_max += 1
			r = self._result.max_cache[e.uuid]
		else:
			self.simplify()

			c = extra_constraints + (self._claripy.UGE(e, two[0]), self._claripy.UGE(e, two[1]))
			r = self._claripy.model_object(self._max(e, extra_constraints=c), result=self._result)

		if len(extra_constraints) == 0:
			self._result.max_cache[e.uuid] = r
			self.add([self._claripy.ULE(e, r)], invalidate_cache=False)

		return r

	def min(self, e, extra_constraints=()):
		global cached_min
		extra_constraints = self._constraint_filter(extra_constraints)

		if len(extra_constraints) == 0:
			for b in self._claripy.model_backends:
				try: return b.min_expr(e, result=self._result)
				except BackendError: pass

		two = self.eval(e, 2, extra_constraints=extra_constraints)
		if len(two) == 0: raise UnsatError("unsat during min()")
		elif len(two) == 1: return two[0]

		if len(extra_constraints) == 0 and e.uuid in self._result.min_cache:
			cached_min += 1
			r = self._result.min_cache[e.uuid]
		else:
			self.simplify()

			c = extra_constraints + (self._claripy.ULE(e, two[0]), self._claripy.ULE(e, two[1]))
			r = self._claripy.model_object(self._min(e, extra_constraints=c), result=self._result)

		if len(extra_constraints) == 0:
			self._result.min_cache[e.uuid] = r
			self.add([self._claripy.UGE(e, r)], invalidate_cache=False)

		return r

	def solution(self, e, v, extra_constraints=()):
		try:
			extra_constraints = self._constraint_filter(extra_constraints)
		except UnsatError:
			return False

		if len(extra_constraints) == 0:
			for b in self._claripy.model_backends:
				try: return b.min_expr(e, result=self._result)
				except BackendError: pass

		b = self._solution(e, v, extra_constraints=extra_constraints)
		if b == False and len(extra_constraints) > 0:
			self.add([e != v], invalidate_cache=False)
		return b

	#
	# These are the functions that actually talk to the backends
	#

	def _solve(self, extra_constraints=()):
		# check it!
		l.debug("Solver.solve() checking SATness of %d constraints", len(self.constraints))
		for b in self._claripy.solver_backends:
			try:
				s = self._get_solver(b)
				l.debug("... trying %s", b)

				a = time.time()
				r = b.results_exprs(s, extra_constraints, generic_model=True)
				b = time.time()

				l_timing.debug("... %s in %s seconds", r.sat, b - a)
				return r
			except BackendError as be:
				l.debug("... BackendError: %s", be)

		raise ClaripySolverError("all solver backends failed for Solver._solve")

	def _eval(self, e, n, extra_constraints=()):
		l.debug("solver._eval(%d) with %d extra_constraints", n, len(extra_constraints))

		for b in self._claripy.solver_backends:
			try:
				l.debug("... trying backend %s", b.__class__.__name__)
				results = b.eval_expr(self._get_solver(b), e, n, extra_constraints=extra_constraints, result=self._result)
				return [ self._claripy.model_object(r) for r in results ]
			except BackendError as be:
				l.debug("... BackendError: %s", be)

		raise ClaripySolverError("all solver backends failed for Solver._eval")

	def _max(self, e, extra_constraints=()):
		l.debug("Solver.max() with %d extra_constraints", len(extra_constraints))
		for b in self._claripy.solver_backends:
			try:
				return b.max_expr(self._get_solver(b), e, extra_constraints=extra_constraints, result=self._result)
			except BackendError as be:
				l.debug("... BackendError: %s", be)
		raise ClaripySolverError("all solver backends failed for Solver._max")

	def _min(self, e, extra_constraints=()):
		l.debug("Solver.min() with %d extra_constraints", len(extra_constraints))
		for b in self._claripy.solver_backends:
			try:
				return b.min_expr(self._get_solver(b), e, extra_constraints=extra_constraints, result=self._result)
			except BackendError as be:
				l.debug("... BackendError: %s", be)
		raise ClaripySolverError("all solver backends failed for Solver._min")

	def _solution(self, e, v, extra_constraints=()):
		for b in self._claripy.solver_backends:
			try:
				return b.solution_expr(self._get_solver(b), e, v, extra_constraints=extra_constraints)
			except BackendError as be:
				l.debug("... BackendError: %s", be)
		raise ClaripySolverError("all solver backends failed for Solver._solution")

	#
	# Serialization and such.
	#

	def downsize(self): #pylint:disable=R0201
		self._solver_states = { }
		self._to_add = { }

	#
	# Merging and splitting
	#

	def finalize(self):
		raise NotImplementedError()

	def branch(self):
		raise NotImplementedError()

	def merge(self, others, merge_flag, merge_values):
		merged = self.__class__(self._claripy, timeout=self._timeout)
		merged._simplified = False
		options = [ ]

		for s, v in zip([self]+others, merge_values):
			options.append(self._claripy.And(*([ merge_flag == v ] + s.constraints)))
		merged.add([self._claripy.Or(*options)])
		return merged

	def combine(self, others):
		combined = self.__class__(self._claripy, timeout=self._timeout)
		combined._simplified = False

		combined.add(self.constraints) #pylint:disable=E1101
		for o in others:
			combined.add(o.constraints)
		return combined

	def split(self):
		results = [ ]
		l.debug("Splitting!")
		for variables,c_list in self._independent_constraints():
			l.debug("... got %d constraints with %d variables", len(c_list), len(variables))

			s = self.__class__(self._claripy, timeout=self._timeout)
			s._simplified = False
			s.add(c_list)
			results.append(s)
		return results

from ..result import Result
from ..expression import E
from ..errors import UnsatError, BackendError, ClaripySolverError
