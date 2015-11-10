#!/usr/bin/env python

import logging
l = logging.getLogger("claripy.frontends.light_frontend")

from ..frontend import Frontend

class LightFrontend(Frontend):
    def __init__(self, solver_backend, **kwargs):
        Frontend.__init__(self, **kwargs)
        self.constraints = [ ]
        self._constraint_hashes = set()
        self.variables = set()
        self._finalized = False
        self._solver_backend = solver_backend

    #
    # Storable support
    #

    def _ana_getstate(self):
        if not self._simplified: self.simplify()
        self.finalize()
        return self._solver_backend.__class__.__name__, self.constraints, self.variables, Frontend._ana_getstate(self)

    def _ana_setstate(self, s):
        solver_backend_name, self.constraints, self.variables, base_state = s
        Frontend._ana_setstate(self, base_state)
        self._solver_backend = _backends[solver_backend_name]
        self._finalized = True

    #
    # Constraint management
    #

    def independent_constraints(self):
        return self._split_constraints(self.constraints)

    #
    # Light functionality
    #

    def _add_constraints(self, constraints, invalidate_cache=True):
        new_constraints = [ c for c in constraints if hash(c) not in self._constraint_hashes ]
        self.constraints += new_constraints
        for c in new_constraints:
            self.variables.update(c.variables)
            self._constraint_hashes.add(hash(c))
        return new_constraints


    def _simplify(self):
        if len(self.constraints) == 0:
            return

        self.constraints = [ simplify(And(*self.constraints)) ]

        # we only add to the constraint hashes because we want to
        # prevent previous (now simplified) constraints from
        # being re-added
        self._constraint_hashes.add(hash(self.constraints[0]))

        # generate UUIDs for every constraint
        for c in self.constraints:
            if isinstance(c, Base): c.make_uuid()

        self._simplified = True
        return self.constraints

    def _solve(self, extra_constraints=(), exact=None, cache=None):
        return SatResult(approximation=True)

    def _satisfiable(self, extra_constraints=(), exact=None, cache=None):
        return self.solve(extra_constraints=extra_constraints, exact=exact, cache=cache).sat

    def _eval(self, e, n, extra_constraints=(), exact=None, cache=None):
        if len(extra_constraints) == 0:
            try: return self._solver_backend.eval(e, n, result=self.result)
            except BackendError: pass

        raise ClaripyFrontendError("Light solver can't handle this eval().")

    def _max(self, e, extra_constraints=(), exact=None, cache=None):
        if len(extra_constraints) == 0:
            try: return self._solver_backend.max(e, result=self.result)
            except BackendError: pass

        raise ClaripyFrontendError("Light solver can't handle this max().")

    def _min(self, e, extra_constraints=(), exact=None, cache=None):
        if len(extra_constraints) == 0:
            try: return self._solver_backend.min(e, result=self.result)
            except BackendError: pass

        raise ClaripyFrontendError("Light solver can't handle this min().")

    def _solution(self, e, v, extra_constraints=(), exact=None, cache=None):
        if len(extra_constraints) == 0:
            try: return self._solver_backend.solution(e, v, result=self.result)
            except BackendError: pass

        raise ClaripyFrontendError("Light solver can't handle this solution().")

    #
    # Serialization and such.
    #

    def downsize(self):
        Frontend.downsize(self)

    #
    # Merging and splitting
    #

    def finalize(self):
        self._finalized = True

    def _blank_copy(self):
        return LightFrontend(self._solver_backend, cache=self._cache)

    def branch(self):
        s = Frontend.branch(self)
        s.constraints = list(self.constraints)
        s.variables = set(self.variables)
        s._constraint_hashes = set(self._constraint_hashes)
        self.finalize()
        s.finalize()
        return s

    def merge(self, others, merge_flag, merge_values):
        merged = self._blank_copy()
        merged._simplified = False
        options = [ ]

        for s, v in zip([self]+others, merge_values):
            options.append(And(*([ merge_flag == v ] + s.constraints)))
        merged.add([Or(*options)])

        return self._solver_backend is backend_z3, merged

    def combine(self, others):
        combined = self._blank_copy()
        combined._simplified = False

        combined.add(self.constraints) #pylint:disable=E1101
        for o in others:
            combined.add(o.constraints)
        return combined

    def split(self):
        results = [ ]
        l.debug("Splitting!")
        for variables,c_list in self.independent_constraints():
            l.debug("... got %d constraints with %d variables", len(c_list), len(variables))

            s = self._blank_copy()
            s._simplified = False
            s.add(c_list)
            results.append(s)
        return results

from ..result import SatResult
from ..errors import BackendError, ClaripyFrontendError
from .. import backend_z3
from ..ast.base import Base, simplify
from ..ast.bool import And, Or
from .. import _backends
