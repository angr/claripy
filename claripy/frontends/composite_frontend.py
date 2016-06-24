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
        self._unsat = False

    def _blank_copy(self, c):
        super(CompositeFrontend, self)._blank_copy(c)
        c._solvers = { }
        c._template_frontend = self._template_frontend
        c._unsat = False

    def _copy(self, c):
        super(CompositeFrontend, self)._copy(c)
        c._unsat = self._unsat

        for s in self._solver_list:
            c_s = s.branch()
            for v in c_s.variables:
                c._solvers[v] = c_s

        return c


    #
    # Serialization stuff
    #

    def _ana_getstate(self):
        return self._solvers, self._template_frontend, self._unsat, super(CompositeFrontend, self)._ana_getstate()

    def _ana_setstate(self, s):
        self._solvers, self._template_frontend, self._unsat, base_state = s
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

    #
    # Solver list management
    #

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

    def _merged_solver_for(self, names=None, lst=None, lst2=None, e=None, v=None):
        if names is None:
            names = set()
        if e is not None and isinstance(e, Base):
            names.update(e.variables)
        if v is not None and isinstance(v, Base):
            names.update(v.variables)
        if lst is not None:
            for e in lst:
                if isinstance(e, Base):
                    names.update(e.variables)
        if lst2 is not None:
            for e in lst2:
                if isinstance(e, Base):
                    names.update(e.variables)

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
        s = self._merged_solver_for(names=names)
        added = s.add(constraints)
        for v in s.variables | names:
            self._solvers[v] = s
        return added

    def add(self, constraints, **kwargs): #pylint:disable=arguments-differ
        split = self._split_constraints(constraints)
        child_added = [ ]

        l.debug("%s, solvers before: %d", self, len(self._solvers))
        unsure = [ ]
        for names,set_constraints in split:
            if names == { 'CONCRETE' }:
                try:
                    if any(backends.concrete.convert(c) is False for c in set_constraints):
                        self._unsat = True
                except BackendError:
                    unsure.extend(set_constraints)
            else:
                child_added += self._add_dependent_constraints(names, set_constraints, **kwargs)

        l.debug("... solvers after add: %d", len(self._solver_list))

        if len(unsure) > 0:
            for s in self._solver_list:
                s.add(unsure)

        return super(CompositeFrontend, self).add(child_added)

    #
    # Solving
    #

    def _ensure_sat(self, extra_constraints):
        if self._unsat or (len(extra_constraints) == 0 and not self.satisfiable()):
            raise UnsatError("CompositeSolver is already unsat")

    def satisfiable(self, extra_constraints=(), exact=None):
        if self._unsat: return False

        l.debug("%r checking satisfiability...", self)

        if len(extra_constraints) != 0:
            extra_solver = self._merged_solver_for(lst=extra_constraints)
            if not extra_solver.satisfiable(extra_constraints=extra_constraints, exact=exact):
                return False

            r = all(
                s.satisfiable(exact=exact) for s in
                self._solver_list if s.variables.isdisjoint(extra_solver.variables)
            )
            self._reabsorb_solver(extra_solver)
            return r
        else:
            return all(s.satisfiable(exact=exact) for s in self._solver_list)

    def eval(self, e, n, extra_constraints=(), exact=None):
        self._ensure_sat(extra_constraints=extra_constraints)

        ms = self._merged_solver_for(e=e, lst=extra_constraints)
        r = ms.eval(e, n, extra_constraints=extra_constraints, exact=exact)
        self._reabsorb_solver(ms)
        return r

    def batch_eval(self, exprs, n, extra_constraints=(), exact=None):
        self._ensure_sat(extra_constraints=extra_constraints)

        ms = self._merged_solver_for(lst2=exprs, lst=extra_constraints)
        r = ms.batch_eval(exprs, n, extra_constraints=extra_constraints, exact=exact)
        self._reabsorb_solver(ms)
        return r

    def max(self, e, extra_constraints=(), exact=None):
        self._ensure_sat(extra_constraints=extra_constraints)

        ms = self._merged_solver_for(e=e, lst=extra_constraints)
        r = ms.max(e, extra_constraints=extra_constraints, exact=exact)
        self._reabsorb_solver(ms)
        return r

    def min(self, e, extra_constraints=(), exact=None):
        self._ensure_sat(extra_constraints=extra_constraints)

        ms = self._merged_solver_for(e=e, lst=extra_constraints)
        r = ms.min(e, extra_constraints=extra_constraints, exact=exact)
        self._reabsorb_solver(ms)
        return r

    def solution(self, e, v, extra_constraints=(), exact=None):
        self._ensure_sat(extra_constraints=extra_constraints)

        ms = self._merged_solver_for(e=e, v=v, lst=extra_constraints)
        r = ms.solution(e, v, extra_constraints=extra_constraints, exact=exact)
        self._reabsorb_solver(ms)
        return r

    def is_true(self, e, extra_constraints=(), exact=None):
        self._ensure_sat(extra_constraints=extra_constraints)

        ms = self._merged_solver_for(e=e, lst=extra_constraints)
        r = ms.is_true(e, extra_constraints=extra_constraints, exact=exact)
        self._reabsorb_solver(ms)
        return r

    def is_false(self, e, extra_constraints=(), exact=None):
        self._ensure_sat(extra_constraints=extra_constraints)

        ms = self._merged_solver_for(e=e, lst=extra_constraints)
        r = ms.is_false(e, extra_constraints=extra_constraints, exact=exact)
        self._reabsorb_solver(ms)
        return r

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
    # Evaluation and caching
    #

    def _reabsorb_solver(self, s):
        if isinstance(s, ModelCacheMixin):
            done = set()
            for ns in s.split():
                os = self._solvers[next(iter(ns.variables))]
                if os in done:
                    continue
                done.add(os)
                new_models = [ nm for nm in ns._models if not any(nm == om for om in os._models) ]
                os._models.extend(new_models)

    #
    # Merging and splitting
    #

    def finalize(self):
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
        return [ s.branch() for s in self._solver_list ]

from ..ast import Base
from .. import backends
from ..errors import BackendError, UnsatError
from .model_cache_mixin import ModelCacheMixin
