import logging
l = logging.getLogger("claripy.frontends.composite_frontend")

import itertools
symbolic_count = itertools.count()

from .constrained_frontend import ConstrainedFrontend

class CompositeFrontend(ConstrainedFrontend):
    def __init__(self, template_frontend, **kwargs):
        super(CompositeFrontend, self).__init__(**kwargs)
        self._solvers = { }
        self._template_frontend = template_frontend

    def _blank_copy(self, c):
        super(CompositeFrontend, self)._blank_copy(c)
        c._solvers = { }
        c._template_frontend = self._template_frontend

    def _copy(self, c):
        super(CompositeFrontend, self)._copy(c)
        for s in self._solver_list:
            c_s = s.branch()
            if len(c_s.variables) == 0:
                c._solvers['CONCRETE'] = c_s
            else:
                for v in c_s.variables:
                    c._solvers[v] = c_s

        return c


    #
    # Serialization stuff
    #

    def _ana_getstate(self):
        return self._solvers, self._template_frontend, super(CompositeFrontend, self)._ana_getstate()

    def _ana_setstate(self, s):
        self._solvers, self._template_frontend, base_state = s
        super(CompositeFrontend, self)._ana_setstate(base_state)

    def downsize(self):
        for e in self._solvers.values():
            e.downsize()

    #
    # Frontend management
    #

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
        return set(self._solvers.keys())

    # this is really hacky, but we want to avoid having our variables messed with
    @variables.setter
    def variables(self, v):
        pass

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
            return self._template_frontend.blank_copy()
        elif len(solvers) == 1:
            l.debug("... got one solver")
            return solvers[0]
        else:
            l.debug(".... combining %d solvers", len(solvers))
            return solvers[0].combine(solvers[1:])

    def _shared_solvers(self, others):
        """
        Returns a sequence of the solvers that self and others share.
        """

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
        added = s.add(constraints)
        for v in s.variables | names:
            self._solvers[v] = s
        return added

    def add(self, constraints, invalidate_cache=True): #pylint:disable=arguments-differ
        added = super(CompositeFrontend, self).add(constraints)

        if not invalidate_cache:
            l.warning("ignoring non-invalidating constraints")
            return

        split = self._split_constraints(added)
        child_added = [ ]

        l.debug("%s, solvers before: %d", self, len(self._solvers))
        for names,set_constraints in split:
            child_added += self._add_dependent_constraints(names, set_constraints)
        l.debug("... solvers after add: %d", len(self._solver_list))

        return added

    #
    # Solving
    #

    def satisfiable(self, extra_constraints=(), exact=None):
        l.debug("%r checking satisfiability...", self)

        if len(extra_constraints) != 0:
            extra_vars = frozenset.union(*(a.variables for a in extra_constraints))
            extra_solver = self._merged_solver_for(extra_vars)
            if not extra_solver.satisfiable(extra_constraints=extra_constraints, exact=exact):
                return False

            return all(
                s.satisfiable(exact=exact) for s in
                self._solver_list if s.variables.isdisjoint(extra_solver.variables)
            )
        else:
            return all(s.satisfiable(exact=exact) for s in self._solver_list)

    def _all_variables(self, e, extra_constraints=()): #pylint:disable=no-self-use
        all_vars = e.variables
        if len(extra_constraints) != 0:
            all_vars |= frozenset.union(*(a.variables for a in extra_constraints))
        return all_vars

    def eval(self, e, n, extra_constraints=(), exact=None):
        return self._merged_solver_for(self._all_variables(e, extra_constraints=extra_constraints)).eval(e, n, extra_constraints=extra_constraints, exact=exact)

    def batch_eval(self, exprs, n, extra_constraints=(), exact=None):

        the_solver = None
        for expr in exprs:
            s = self._merged_solver_for(self._all_variables(expr, extra_constraints=extra_constraints))
            if the_solver is None:
                the_solver = s
            elif the_solver is not s:
                raise ClaripyFrontendError("having expressions across multiple solvers is not supported by _batch_eval() right now")

        return the_solver.batch_eval(exprs, n, extra_constraints=extra_constraints, exact=exact)

    def max(self, e, extra_constraints=(), exact=None):
        return self._merged_solver_for(self._all_variables(e, extra_constraints=extra_constraints)).max(e, extra_constraints=extra_constraints, exact=exact)

    def min(self, e, extra_constraints=(), exact=None):
        return self._merged_solver_for(self._all_variables(e, extra_constraints=extra_constraints)).min(e, extra_constraints=extra_constraints, exact=exact)

    def solution(self, e, n, extra_constraints=(), exact=None):
        return self._merged_solver_for(self._all_variables(e, extra_constraints=extra_constraints)).solution(e, n, extra_constraints=extra_constraints, exact=exact)

    def is_true(self, e, extra_constraints=(), exact=None):
        return self._merged_solver_for(self._all_variables(e, extra_constraints=extra_constraints)).is_true(e, extra_constraints=extra_constraints, exact=exact)

    def is_false(self, e, extra_constraints=(), exact=None):
        return self._merged_solver_for(self._all_variables(e, extra_constraints=extra_constraints)).is_false(e, extra_constraints=extra_constraints, exact=exact)

    def simplify(self):
        new_constraints = [ ]

        l.debug("Simplifying %r with %d solvers", self, len(self._solver_list))
        for s in self._solver_list:
            if s._simplified:
                new_constraints += s.constraints
                continue

            l.debug("... simplifying child solver %r", s)
            s.simplify()
            l.debug("... splitting child solver %r", s)
            split = s.split()

            l.debug("... split solver %r into %d parts", s, len(split))
            l.debug("... variable counts: %s", [ len(ss.variables) for ss in split ])
            if len(split) > 1:
                for s in split:
                    new_constraints += s.constraints
                    for v in s.variables:
                        self._solvers[v] = s
            else:
                new_constraints += s.constraints
        l.debug("... after-split, %r has %d solvers", self, len(self._solver_list))

        self.constraints = new_constraints
        return new_constraints

    #
    # Merging and splitting
    #

    def finalize(self):
        l.error("CompositeFrontend.finalize is incomplete. This represents a big issue.")
        for s in self._solver_list:
            s.finalize()

    @property
    def timeout(self):
        return self._template_frontend.timeout

    @timeout.setter
    def timeout(self, t):
        self._template_frontend.timeout = t
        for s in self._solver_list:
            s.timeout = t

    def merge(self, others, merge_flag, merge_values):
        l.debug("Merging %s with %d other solvers.", self, len(others))
        merged = self.blank_copy()
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
                s = self.blank_copy()
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

    def combine(self, others):
        combined = self.blank_copy()
        combined._simplified = False
        combined.add(self.constraints)
        for o in others:
            combined.add(o.constraints)
        return combined

    def split(self):
        return [ s.branch() for s in self._solver_list if len(s.variables) > 0 ]

from ..errors import ClaripyFrontendError
