import logging
l = logging.getLogger("claripy.solvers.composite_solver")

import itertools

symbolic_count = itertools.count()

from .solver import Solver
from .branching_solver import BranchingSolver

class CompositeSolver(Solver):
    def __init__(self, claripy, timeout=None, solver_class=BranchingSolver, **kwargs):
        Solver.__init__(self, claripy, timeout=timeout, **kwargs)
        self._results = None
        self._solvers = { }
        self._solver_class = solver_class

        self._solvers['CONCRETE'] = self._merged_solver_for({'CONCRETE'})

    #
    # Serialization stuff
    #

    def _claripy_getstate(self):
        return self._solvers, self._solver_class, self._results

    def _claripy_setstate(self, s):
        self._solvers, self._solver_class, self._results = s

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
        return set(self._solvers.keys()) - { 'CONCRETE' }

    @property
    def constraints(self):
        return sum([ s.constraints for s in self._solver_list ], [ ])

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
        l.debug("composite_solver._merged_solver_for() running with %d names", len(names))
        solvers = self._solvers_for_variables(names)
        if len(solvers) == 0:
            l.debug("... creating new solver")
            return self._solver_class(self._claripy, timeout=self._timeout)
        elif len(solvers) == 1:
            l.debug("... got one solver")
            return solvers[0]
        else:
            l.debug(".... combining %d solvers", len(solvers))
            return solvers[0].combine(solvers[1:])

    def _shared_solvers(self, others):
        '''
        Returns a sequence of the solvers that self and others share.
        '''

        solvers_by_id = { s.uuid: s for s in self._solver_list }
        common_solvers = set(solvers_by_id.keys())
        other_sets = [ { s.uuid for s in cs._solver_list } for cs in others ]
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

    def _add_dependent_constraints(self, names, constraints):
        l.debug("Adding %d constraints to %d names", len(constraints), len(names))
        s = self._merged_solver_for(names)
        s.add(constraints)
        for v in s.variables | names:
            self._solvers[v] = s

    def add(self, constraints, invalidate_cache=True):
        try:
            filtered = self._constraint_filter(constraints)
        except UnsatError:
            self._result = Result(False, { })
            self._add_dependent_constraints({ 'CONCRETE' }, [ self._claripy.BoolVal(False) ])
            return

        if not invalidate_cache:
            l.warning("ignoring non-invalidating constraints")
            return

        if filtered is None or len(filtered) == 0:
            return

        split = self._independent_constraints(constraints=filtered)

        #print "AFTER SPLIT:", split

        l.debug("%s, solvers before: %d", self, len(self._solvers))

        for names,set_constraints in split:
            self._add_dependent_constraints(names, set_constraints)

        l.debug("... solvers after add: %d", len(self._solver_list))

    #
    # Solving
    #

    def _solve(self, extra_constraints=()):
        l.debug("%r checking satisfiability...", self)

        if len(extra_constraints) != 0:
            extra_vars = frozenset.union(*(a.variables for a in extra_constraints))
            solvers = [ self._merged_solver_for(extra_vars) ]
            for s in self._solver_list:
                if len(s.variables | solvers[0].variables) == 0:
                    solvers.append(s)
        else:
            solvers = self._solver_list

        model = { }
        satness = True

        for s in solvers:
            if not s.satisfiable(extra_constraints=extra_constraints if s is solvers[0] else ()):
                l.debug("... %r: False", s)
                satness = False
                break

            l.debug("... %r: True", s)
            model.update(s._result.model)

        l.debug("... ok!")
        return Result(satness, model)

    def _all_variables(self, e, extra_constraints=()): #pylint:disable=no-self-use
        all_vars = e.variables
        if len(extra_constraints) != 0:
            all_vars |= frozenset.union(*(a.variables for a in extra_constraints))
        if len(all_vars) == 0:
            all_vars = { 'CONCRETE' }
        return all_vars


    def eval(self, e, n, extra_constraints=()):
        return self._merged_solver_for(self._all_variables(e, extra_constraints=extra_constraints)).eval(e, n, extra_constraints=extra_constraints)

    def max(self, e, extra_constraints=()):
        return self._merged_solver_for(self._all_variables(e, extra_constraints=extra_constraints)).max(e, extra_constraints=extra_constraints)

    def min(self, e, extra_constraints=()):
        return self._merged_solver_for(self._all_variables(e, extra_constraints=extra_constraints)).min(e, extra_constraints=extra_constraints)

    def solution(self, e, n, extra_constraints=()):
        return self._merged_solver_for(self._all_variables(e, extra_constraints=extra_constraints)).solution(e, n, extra_constraints=extra_constraints)

    #
    # Merging and splitting
    #

    def finalize(self):
        l.error("CompositeSolver.finalize is incomplete. This represents a big issue.")
        for s in self._solver_list:
            s.finalize()

    def simplify(self):
        l.debug("Simplifying %r with %d solvers", self, len(self._solver_list))
        for s in self._solver_list:
            if s._simplified:
                continue

            l.debug("... simplifying child solver %r", s)
            s.simplify()
            l.debug("... splitting child solver %r", s)
            split = s.split()

            l.debug("... split solver %r into %d parts", s, len(split))
            l.debug("... variable counts: %s", [ len(ss.variables) for ss in split ])
            if len(split) > 1:
                for s in split:
                    for v in s.variables:
                        self._solvers[v] = s
        l.debug("... after-split, %r has %d solvers", self, len(self._solver_list))

    def branch(self):
        c = CompositeSolver(self._claripy, timeout=self._timeout)
        for s in self._solver_list:
            c_s = s.branch()
            for v in c_s.variables:
                c._solvers[v] = c_s

        if self._result is not None:
            c._result = self._result.branch()

        return c

    def merge(self, others, merge_flag, merge_values):
        l.debug("Merging %s with %d other solvers.", self, len(others))
        merged = CompositeSolver(self._claripy, timeout=self._timeout)
        common_solvers = self._shared_solvers(others)
        common_ids = { s.uuid for s in common_solvers }
        l.debug("... %s common solvers", len(common_solvers))

        for s in common_solvers:
            for v in s.variables:
                merged._solvers[v] = s.branch()

        noncommon_solvers = [ [ s for s in cs._solver_list if s.uuid not in common_ids ] for cs in [self]+others ]

        l.debug("... merging noncommon solvers")
        combined_noncommons = [ ]
        for ns in noncommon_solvers:
            l.debug("... %d", len(ns))
            if len(ns) == 0:
                s = self._solver_class(self._claripy, timeout=self._timeout)
                s.add(True)
                combined_noncommons.append(s)
            elif len(ns) == 1:
                combined_noncommons.append(ns[0])
            else:
                combined_noncommons.append(ns[0].combine(ns[1:]))

        _, merged_noncommon = combined_noncommons[0].merge(combined_noncommons[1:], merge_flag, merge_values)
        for v in merged_noncommon.variables:
            merged._solvers[v] = merged_noncommon

        return True, merged

    #def combine(self, others):
    #    raise NotImplementedError()

from ..result import Result
from ..errors import UnsatError
