import logging
l = logging.getLogger("claripy.solvers.composite_solver")

import itertools
symbolic_count = itertools.count()
from copy import copy

from .solver import Solver
from .branching_solver import BranchingSolver

class CompositeSolver(Solver):
	def __init__(self, claripy, solver_backend=None, results_backend=None, timeout=None, solver_class=BranchingSolver):
		Solver.__init__(self, claripy, solver_backend=solver_backend, results_backend=results_backend, timeout=timeout)
		self._results = None
		self._solvers = { }
		self._solver_class = solver_class

	@property
	def _solver_list(self):
		seen_solvers = set()
		solver_list = [ ]
		for s in self._solvers.itervalues():
			if id(s) in seen_solvers: continue
			seen_solvers.add(id(s))
			solver_list.append(s)
		return solver_list

	@property
	def variables(self):
		return self._solvers.keys()

	def _solvers_for_variables(self, names):
		seen_solvers = set()
		existing_solvers = [ ]
		for n in names:
			if n not in self._solvers: continue
			s = self._solvers[n]

			if id(s) in seen_solvers: continue
			seen_solvers.add(id(s))
			existing_solvers.append(s)
		return existing_solvers

	def _merged_solver_for(self, names):
		solvers = self._solvers_for_variables(names)
		if len(solvers) == 1:
			return solvers[0]
		else:
			return solvers[0].combine(solvers[1:])

	def _shared_solvers(self, others):
		'''
		Returns a sequence of the solvers that self and others share.
		'''

		solvers_by_id = { s._id: s for s in self._solver_list }
		common_solvers = set(solvers_by_id.keys())
		other_sets = [ { s._id for s in cs._solver_list } for cs in others ]
		for o in other_sets: common_solvers &= o

		return [ solvers_by_id[s] for s in common_solvers ]

	def _variable_sets(self):
		return { s.variables for s in self._solver_list }

	def _shared_varsets(self, others):
		common_varsets = self._variable_sets()
		for o in others: common_varsets &= o.all_varsets()
		return common_varsets

	#
	# Constraints
	#

	def add(self, *constraints, **kwargs):
		if len(constraints) == 0:
			return

		self._result = None

		#print "GOT CONSTRAINTS:", constraints

		# first, flatten the constraints
		split = self._independent_constraints(constraints=constraints)

		#print "AFTER SPLIT:", split

		l.debug("%s, solvers before: %d", self, len(self._solvers))
		for names, set_constraints in split:
			l.debug("Checking %d constraints for names %s", len(set_constraints), names)

			#print "=============================="
			#for i in set_constraints:
			#	print "-------------------------"
			#	print i
			#print "==========================---="

			# this signifies that we are setting some variable to be concrete
			#if len(names) == 1:
			#	self._time_to_split = True

			# handle concrete-only constraints
			if len(names) == 0:
				names = { "CONCRETE" }

			existing_solvers = self._solvers_for_variables(names)

			# totally unrelated to existing constraints
			if len(existing_solvers) == 0:
				l.debug("... got a new set of constraints!")
				new_solver = self._solver_class(self._claripy, results_backend=self._results_backend, solver_backend=self._solver_backend, timeout=self._timeout)

			# fits within an existing solver
			elif len(existing_solvers) == 1:
				# TODO: split
				l.debug("... constraints fit into an existing solver.")
				new_solver = existing_solvers[0]

			# have to merge two solvers
			else:
				l.debug("... merging %d solvers.", len(existing_solvers))
				new_solver = existing_solvers[0].combine(existing_solvers[1:])

			# add the constraint tot he new solver
			new_solver.add(*set_constraints)

			# sanity checking
			if len(names - new_solver.variables - {"CONCRETE"}) > 0:
				raise Exception("Something went wrong with solver merging. Nag Yan!")

			# invalidate the solution cache and update solvers, and don't forget the concrete one!
			for n in new_solver.variables | (names & {"CONCRETE"}):
				self._solvers[n] = new_solver
		l.debug("Solvers after: %d", len(self._solvers))

	#
	# Solving
	#

	def check(self):
		l.debug("%r checking satisfiability...", self)

		model = { }
		satness = sat

		for s in self._solver_list:
			if not s.check() == sat:
				l.debug("... %r: False", s)
				satness = unsat
				break

			l.debug("... %r: True", s)
			model.update(s._results.model)

		l.debug("... ok!")
		self._results = Result(satness, model)
		return satness

	def _eval(self, e, n, extra_constraints=None):
		self._merged_solver_for(e.variables).eval(e, n, extra_constraints=extra_constraints)

	def _max(self, e, extra_constraints=None):
		self._merged_solver_for(e.variables).max(e, extra_constraints=extra_constraints)

	def _min(self, e, extra_constraints=None):
		self._merged_solver_for(e.variables).min(e, extra_constraints=extra_constraints)

	#
	# Merging and splitting
	#

	def finalize(self):
		raise NotImplementedError()

	def simplify(self):
		for s in self._solvers:
			s.simplify()
			split = s.split()
			if len(split) > 1:
				for s in split:
					for v in s.variables:
						self._solvers[v] = s

	def branch(self):
		c = CompositeSolver(self._claripy, solver_backend=self._solver_backend, results_backend=self._results_backend, timeout=self._timeout)
		for s in self._solvers:
			c_s = s.branch()
			for v in c_s.variables:
				c._solvers[v] = c_s

		if self._result is not None:
			c._result = self._result.branch()

		return c

	def merge(self, others, merge_flag, merge_values):
		l.debug("Merging %s with %d other solvers.", self, len(others))
		merged = CompositeSolver(self._claripy, results_backend=self._results_backend, solver_backend=self._solver_backend, timeout=self._timeout)
		common_solvers = self._shared_solvers(others)
		common_ids = { s._id for s in common_solvers }
		l.debug("... %s common solvers", len(common_solvers))

		merged.variables = copy(self.variables)

		for s in common_solvers:
			for v in s.variables:
				merged._solvers[v] = s.branch()

		noncommon_solvers = [ [ s for s in cs._solvers if s._id not in common_ids ] for cs in [self]+others ]

		l.debug("... merging noncommon solvers")
		combined_noncommons = [ ]
		for ns in noncommon_solvers:
			l.debug("... %d", len(ns))
			if len(ns) == 0:
				s = self._solver_class(self._claripy, results_backend=self._results_backend, solver_backend=self._solver_backend, timeout=self._timeout)
				s.add(True)
				combined_noncommons.append(s)
			elif len(ns) == 1:
				combined_noncommons.append(ns[0])
			else:
				combined_noncommons.append(ns[0].combine(ns[1:]))

		merged_noncommon = combined_noncommons[0].merge(combined_noncommons[1:], merge_flag, merge_values)
		for v in merged_noncommon.variables:
			merged._solvers[v] = merged_noncommon

		return merged

	def combine(self, others):
		raise NotImplementedError()

from ..result import Result, sat, unsat
