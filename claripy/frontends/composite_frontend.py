import logging
l = logging.getLogger("claripy.frontends.composite_frontend")

import weakref
import itertools
symbolic_count = itertools.count()

from .constrained_frontend import ConstrainedFrontend

class CompositeFrontend(ConstrainedFrontend):
    def __init__(self, template_frontend, **kwargs):
        super(CompositeFrontend, self).__init__(**kwargs)
        self._solvers = { }
        self._owned_solvers = weakref.WeakKeyDictionary()
        self._template_frontend = template_frontend
        self._unsat = False

    def _blank_copy(self, c):
        super(CompositeFrontend, self)._blank_copy(c)
        c._owned_solvers = weakref.WeakKeyDictionary()
        c._solvers = { }
        c._template_frontend = self._template_frontend
        c._unsat = False

    def _copy(self, c):
        super(CompositeFrontend, self)._copy(c)
        c._unsat = self._unsat

        c._solvers = dict(self._solvers)
        self._owned_solvers = weakref.WeakKeyDictionary() # for the COW
        return c


    #
    # Serialization stuff
    #

    def _ana_getstate(self):
        return self._solvers, self._template_frontend, self._unsat, super(CompositeFrontend, self)._ana_getstate()

    def _ana_setstate(self, s):
        self._solvers, self._template_frontend, self._unsat, base_state = s
        self._owned_solvers = weakref.WeakKeyDictionary({s:True for s in self._solver_list})
        super(CompositeFrontend, self)._ana_setstate(base_state)

    def downsize(self):
        for e in self._solver_list:
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
        if len(self._solver_list) == 0:
            return set()
        else:
            return set.union(*[s.variables for s in self._solver_list])

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

    @staticmethod
    def _names_for(names=None, lst=None, lst2=None, e=None, v=None):
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
        return names

    def _merged_solver_for(self, *args, **kwargs):
        return self._solver_for_names(self._names_for(*args, **kwargs))

    def _solver_for_names(self, names):
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

    def _split_child(self, s):
        ss = s.split()
        if len(ss) == 1:
            return [ s ]

        l.debug("... split solver %r into %d parts", s, len(ss))
        l.debug("... variable counts: %s", [ len(cs.variables) for cs in ss ])

        for ns in ss:
            self._owned_solvers[ns] = True
            self._store_child(ns)

        return ss

    def _reabsorb_solver(self, s):
        try:
            if len(s.variables) == 0 or self._solvers[next(iter(s.variables))] is s:
                return
        except KeyError:
            # this happens when a variable is introduced due to constraint expansion
            return

        if isinstance(s, ModelCacheMixin):
            new_solvers = s.split()
            old_solvers = self._solvers_for_variables(s.variables)
            if len(new_solvers) == len(old_solvers):
                done = set()
                for s in s.split():
                    if s in done:
                        continue
                    done.add(s)
                    v = next(iter(s.variables))
                    self._solvers[v].update(s)
            else:
                for ns in new_solvers:
                    self._owned_solvers[ns] = True
                    self._store_child(ns)

    def _store_child(self, ns, extra_names=frozenset()):
        for v in ns.variables | extra_names:
            #os = self._solvers[v]
            self._solvers[v] = ns

        #if isinstance(s, ModelCacheMixin):
        #   if len(os._models) < len(ns._models):
        #       print "GOT %d NEW MODELS (before: %d)" % (
        #           len(ns._models) - len(os._models), len(os._models)
        #       )
        #   elif len(os._models) > len(ns._models):
        #       print "WARNING: LOST %d NEW MODELS (before: %d)" % (
        #           len(os._models) - len(ns._models), len(os._models)
        #       )
        #   else:
        #       print "Remained at %d models." % len(os._models)

    #
    # Constraints
    #

    def _claim(self, s):
        if s not in self._owned_solvers:
            sc = s.branch()
            self._owned_solvers[sc] = True
            return sc
        else:
            return s

    def _add_dependent_constraints(self, names, constraints, invalidate_cache=True, **kwargs):
        if not invalidate_cache and len(self._solvers_for_variables(names)) > 1:
            l.debug("Ignoring cross-solver helper constraints.")
            return [ ]

        l.debug("Adding %d constraints to %d names", len(constraints), len(names))
        s = self._claim(self._merged_solver_for(names=names))
        added = s.add(constraints, **kwargs)
        self._store_child(s)
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
                s = self._claim(s)
                s.add(unsure)
                self._store_child(s)

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
        #self._ensure_sat(extra_constraints=extra_constraints)

        ms = self._merged_solver_for(e=e, lst=extra_constraints)
        r = ms.is_true(e, extra_constraints=extra_constraints, exact=exact)
        #self._reabsorb_solver(ms)
        return r

    def is_false(self, e, extra_constraints=(), exact=None):
        #self._ensure_sat(extra_constraints=extra_constraints)

        ms = self._merged_solver_for(e=e, lst=extra_constraints)
        r = ms.is_false(e, extra_constraints=extra_constraints, exact=exact)
        #self._reabsorb_solver(ms)
        return r

    def simplify(self):
        if self._unsat:
            return self.constraints

        new_constraints = [ ]

        l.debug("Simplifying %r with %d solvers", self, len(self._solver_list))
        for s in self._solver_list:
            if isinstance(s, SimplifySkipperMixin) and s._simplified:
                new_constraints += s.constraints
                continue

            l.debug("... simplifying child solver %r", s)
            s.simplify()
            results = self._split_child(s)
            for ns in results:
                if isinstance(ns, SimplifySkipperMixin):
                    ns._simplified = True
            new_constraints += s.constraints

        l.debug("... after-split, %r has %d solvers", self, len(self._solver_list))

        self.constraints = new_constraints
        return new_constraints

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

    def merge(self, others, merge_conditions):
        l.debug("Merging %s with %d other solvers.", self, len(others))
        merged = self.blank_copy()
        common_solvers = self._shared_solvers(others)
        common_ids = { s.uuid for s in common_solvers }
        l.debug("... %s common solvers", len(common_solvers))

        for s in common_solvers:
            self._owned_solvers.pop(s, None)
            for o in others:
                o._owned_solvers.pop(s, None)

            for v in s.variables:
                merged._solvers[v] = s

        noncommon_solvers = [ [ s for s in cs._solver_list if s.uuid not in common_ids ] for cs in [self]+others ]

        l.debug("... merging noncommon solvers")
        combined_noncommons = [ ]
        for ns in noncommon_solvers:
            l.debug("... %d", len(ns))
            if len(ns) == 0:
                pass
            elif len(ns) == 1:
                combined_noncommons.append(ns[0])
            else:
                combined_noncommons.append(ns[0].combine(ns[1:]))

        if len(combined_noncommons):
            _, merged_noncommon = combined_noncommons[0].merge(
                combined_noncommons[1:], merge_conditions
            )

            merged._owned_solvers[merged_noncommon] = True
            merged._store_child(merged_noncommon)

        return True, merged

    def combine(self, others):
        combined = self.blank_copy()
        combined.add(self.constraints)
        for o in others:
            combined.add(o.constraints)
        return combined

    def split(self):
        return [ s.branch() for s in self._solver_list ]

from ..ast import Base
from .. import backends
from ..errors import BackendError, UnsatError
from ..frontend_mixins.model_cache_mixin import ModelCacheMixin
from ..frontend_mixins.simplify_skipper_mixin import SimplifySkipperMixin
