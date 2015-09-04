#!/usr/bin/env python

import logging
l = logging.getLogger("claripy.frontends.light_frontend")

from ..frontend import Frontend

class LightFrontend(Frontend):
    def __init__(self, solver_backend):
        Frontend.__init__(self, solver_backend)
        self.constraints = [ ]
        self.variables = set()
        self._finalized = False

    #
    # Storable support
    #

    def _ana_getstate(self):
        if not self._simplified: self.simplify()
        self.finalize()
        return self.constraints, self.variables, Frontend._ana_getstate(self)

    def _ana_setstate(self, s):
        self.constraints, self.variables, base_state = s
        Frontend._ana_setstate(self, base_state)
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
        self.constraints += constraints
        for c in constraints:
            self.variables.update(c.variables)
        return constraints


    def _simplify(self):
        if len(self.constraints) == 0:
            return

        self.constraints = [ simplify(And(*self.constraints)) ]

        # generate UUIDs for every constraint
        for c in self.constraints:
            if isinstance(c, Base): c.make_uuid()

        self._simplified = True
        return self.constraints

    def _solve(self, extra_constraints=()):
        return SatResult(approximation=True)

    def _satisfiable(self, extra_constraints=()):
        return self.solve(extra_constraints=extra_constraints).sat

    def _eval(self, e, n, extra_constraints=()):
        if len(extra_constraints) == 0:
            for b in _eager_backends + [ self._solver_backend ]:
                try: return b.eval(e, n, result=self.result)
                except BackendError: pass

        raise ClaripyFrontendError("Light solver can't handle this eval().")

    def _max(self, e, extra_constraints=()):
        if len(extra_constraints) == 0:
            for b in _eager_backends + [ self._solver_backend ]:
                try: return b.max(e, result=self.result)
                except BackendError: pass

        raise ClaripyFrontendError("Light solver can't handle this max().")

    def _min(self, e, extra_constraints=()):
        extra_constraints = self._constraint_filter(extra_constraints)

        if len(extra_constraints) == 0:
            for b in _eager_backends + [ self._solver_backend ]:
                try: return b.min(e, result=self.result)
                except BackendError: pass

        two = self.eval(e, 2, extra_constraints=extra_constraints)
        if len(two) == 0: raise UnsatError("unsat during min()")
        elif len(two) == 1: return two[0]

        raise ClaripyFrontendError("Light solver can't handle this min().")

    def _solution(self, e, v, extra_constraints=()):
        if len(extra_constraints) == 0:
            for b in _eager_backends + [ self._solver_backend ]:
                try: return b.solution(e, v, result=self.result)
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

    def branch(self):
        s = Frontend.branch(self)
        s.constraints = list(self.constraints)
        s.variables = set(self.variables)
        self.finalize()
        s.finalize()
        return s

    def merge(self, others, merge_flag, merge_values):
        merged = self.__class__(self._solver_backend)
        merged._simplified = False
        options = [ ]

        for s, v in zip([self]+others, merge_values):
            options.append(And(*([ merge_flag == v ] + s.constraints)))
        merged.add([Or(*options)])

        return self._solver_backend is backend_z3, merged

    def combine(self, others):
        combined = self.__class__(self._solver_backend)
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

            s = self.__class__(self._solver_backend)
            s._simplified = False
            s.add(c_list)
            results.append(s)
        return results

from ..result import SatResult
from ..errors import UnsatError, BackendError, ClaripyFrontendError
from .. import _eager_backends, backend_z3
from ..ast.base import Base, simplify
from ..ast.bool import And, Or
