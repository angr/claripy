#!/usr/bin/env python

import logging
l = logging.getLogger("claripy.solvers.solver")

cached_evals = 0
cached_min = 0
cached_max = 0
cached_solve = 0
filter_true = 0
filter_false = 0

from ..storable import Storable

class Solver(Storable):
	def __init__(self, claripy, solver_backend=None, result=None, results_backend=None, timeout=None):
		Storable.__init__(self, claripy)
		self._solver_backend = solver_backend if solver_backend is not None else claripy.solver_backend
		self._results_backend = results_backend if results_backend is not None else claripy.results_backend

		self._finalized = None
		self._result = result
		self._simplified = True
		self._timeout = timeout if timeout is not None else 300000

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
			l.debug("... processing constraint with variables %r", s.variables)

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


	#
	# Solving
	#

	def _constraint_filter(self, ec):
		global filter_true, filter_false
		if ec is None: return None

		fc = [ ]
		for e in ec:
			e_simp = self._solver_backend.simplify_expr(e)
			if not e_simp.symbolic and self._results_backend.convert_expr(e_simp):
				filter_true += 1
				continue
			elif not e_simp.symbolic and not self._results_backend.convert_expr(e_simp):
				filter_false += 1
				raise UnsatError("expressions contain False")

			fc.append(e_simp)

		#print fc
		return fc if len(fc) > 0 else None

	def solve(self, extra_constraints=None):
		global cached_solve
		try:
			extra_constraints = self._constraint_filter(extra_constraints)
		except UnsatError:
			return Result(False, { })

		if self._result is not None and not self._result.sat:
			return self._result

		if extra_constraints is None and self._result is not None:
			cached_solve += 1
			return self._result
		else:
			r = self._solve(extra_constraints=extra_constraints)
			if r.sat or extra_constraints is None:
				self._result = r
			return r

	def satisfiable(self, extra_constraints=None):
		return self.solve(extra_constraints=extra_constraints).sat

	def any(self, expr, extra_constraints=None):
		return self.eval(expr, 1, extra_constraints)[0]

	def eval(self, e, n, extra_constraints=None):
		global cached_evals
		extra_constraints = self._constraint_filter(extra_constraints)

		if type(e) is not E: raise ValueError("Solver got a non-E for e.")

		if not e.symbolic:
			#if extra_constraints is None:
			#	l.warning("returning non-symbolic expression despite having extra_constraints. Could lead to subtle issues in analyses.")
			r = [ self._results_backend.convert_expr(e) ]

		if not self.satisfiable(extra_constraints=extra_constraints): raise UnsatError('unsat')

		if extra_constraints is None:
			if e.uuid in self._result.eval_cache:
				cached_n = self._result.eval_cache[e.uuid][0]
				cached_eval = self._result.eval_cache[e.uuid][1]

				if cached_n >= n:
					r = cached_eval[:n]
				elif len(cached_eval) < cached_n:
					r = cached_eval[:n]
				else:
					n -= cached_n
					extra_constraints = [ e != v for v in cached_eval ]

					o = self._solver_backend.convert_expr(e)
					try:
						r = [ self._results_backend.convert(i, model=self._result.model) for i in self._eval(o, n, extra_constraints=extra_constraints) ]
					except UnsatError:
						r = [ ]

					n += cached_n
					r = cached_eval + r
				cached_evals += cached_n
			else:
				o = self._solver_backend.convert_expr(e)
				r = [ self._results_backend.convert(i, model=self._result.model) for i in self._eval(o, n, extra_constraints=extra_constraints) ]

			self._result.eval_cache[e.uuid] = (n, r)

			# if there are less possible solutions than n (i.e., meaning we got all the solutions for e),
			# add constraints to help the solver out later
			if len(r) < n:
				self.add(self._claripy.Or(*[ e == v for v in r ]))
		else:
			o = self._solver_backend.convert_expr(e)
			r = [ self._results_backend.convert(i, model=self._result.model) for i in self._eval(o, n, extra_constraints=extra_constraints) ]
			if e.uuid not in self._result.eval_cache:
				self._result.eval_cache[e.uuid] = (len(r), r)
		return [ self._results_backend.wrap(i) for i in r ]

	def max(self, e, extra_constraints=None):
		global cached_max
		extra_constraints = self._constraint_filter(extra_constraints)

		two = self.eval(e, 2, extra_constraints=extra_constraints)
		if len(two) == 1: return two[0]

		if extra_constraints is None and e.uuid in self._result.max_cache:
			cached_max += 1
			r = self._result.max_cache[e.uuid]
		else:
			self.simplify()
			o = self._solver_backend.convert_expr(e)
			c = ([ ] if extra_constraints is None else extra_constraints) + [ self._claripy.UGE(e, two[0]), self._claripy.UGE(e, two[1]) ]
			r = self._results_backend.convert(self._max(o, extra_constraints=c), model=self._result.model)

		if extra_constraints is None:
			self._result.max_cache[e.uuid] = r
			self.add(self._claripy.ULE(e, r))

		return self._results_backend.wrap(r)

	def min(self, e, extra_constraints=None):
		global cached_min
		extra_constraints = self._constraint_filter(extra_constraints)

		two = self.eval(e, 2, extra_constraints=extra_constraints)
		if len(two) == 1: return two[0]

		if extra_constraints is None and e.uuid in self._result.min_cache:
			cached_min += 1
			r = self._result.min_cache[e.uuid]
		else:
			self.simplify()
			o = self._solver_backend.convert_expr(e)
			c = ([ ] if extra_constraints is None else extra_constraints) + [ self._claripy.ULE(e, two[0]), self._claripy.ULE(e, two[1]) ]
			r = self._results_backend.convert(self._min(o, extra_constraints=c), model=self._result.model)

		if extra_constraints is None:
			self._result.min_cache[e.uuid] = r
			self.add(self._claripy.UGE(e, r))

		return self._results_backend.wrap(r)

	def solution(self, e, v):
		b = self._solution(e, v)
		if not b: self.add(e != v)
		return b


	#
	# These should be implemented by the solver subclass
	#

	def add(self, *constraints):
		raise NotImplementedError()

	def _solve(self, extra_constraints=None):
		raise NotImplementedError()
	def _eval(self, e, n, extra_constraints=None):
		raise NotImplementedError()
	def _max(self, e, extra_constraints=None):
		raise NotImplementedError()
	def _min(self, e, extra_constraints=None):
		raise NotImplementedError()
	def _solution(self, e, v):
		raise NotImplementedError()

	def eval_value(self, e, n, extra_constraints=None):
		return [ self._results_backend.convert_expr(r) for r in self.eval(e, n, extra_constraints=extra_constraints) ]
	def min_value(self, e, extra_constraints=None):
		return self._results_backend.convert_expr(self.min(e, extra_constraints=extra_constraints))
	def max_value(self, e, extra_constraints=None):
		return self._results_backend.convert_expr(self.max(e, extra_constraints=extra_constraints))
	def any_value(self, expr, extra_constraints=None):
		return self._results_backend.convert_expr(self.eval(expr, 1, extra_constraints)[0])

	#
	# Serialization and such.
	#

	def downsize(self): #pylint:disable=R0201
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
		merged = self.__class__(self._claripy, solver_backend=self._solver_backend, results_backend=self._results_backend, timeout=self._timeout)
		options = [ ]

		for s, v in zip([self]+others, merge_values):
			options.append(self._solver_backend.call('And', [ merge_flag == v ] + s.constraints))
		merged.add(self._solver_backend.call('Or', options))
		return merged

	def combine(self, others):
		combined = self.__class__(self._claripy, solver_backend=self._solver_backend, results_backend=self._results_backend, timeout=self._timeout)

		combined.add(*self.constraints) #pylint:disable=E1101
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

from ..result import UnsatError, Result
from ..expression import E
