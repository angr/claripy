#!/usr/bin/env python

import logging

l = logging.getLogger("claripy.frontends.constrained_frontend")

from ..frontend import Frontend


class ConstrainedFrontend(Frontend):  # pylint:disable=abstract-method
    def __init__(self, **kwargs):
        Frontend.__init__(self, **kwargs)
        self.constraints = []
        self.variables = set()
        self._finalized = False

    def _blank_copy(self, c):
        super(ConstrainedFrontend, self)._blank_copy(c)
        c.constraints = []
        c.variables = set()
        c._finalized = False

    def _copy(self, c):
        super(ConstrainedFrontend, self)._copy(c)
        c.constraints = list(self.constraints)
        c.variables = set(self.variables)

        # finalize both
        self.finalize()
        c.finalize()

    #
    # Storable support
    #

    def _ana_getstate(self):
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
    # Serialization and such.
    #

    def downsize(self):
        Frontend.downsize(self)

    #
    # Merging and splitting
    #

    def finalize(self):
        self._finalized = True

    def merge(self, others, merge_conditions):
        merged = self.blank_copy()
        options = []

        for s,v in zip([self] + others, merge_conditions):
            options.append(And(*([v] + s.constraints)))
        merged.add([Or(*options)])

        return False, merged

    def combine(self, others):
        combined = self.blank_copy()

        combined.add(self.constraints)    # pylint:disable=E1101
        for o in others:
            combined.add(o.constraints)
        return combined

    def split(self):
        results = []
        l.debug("Splitting!")
        for variables, c_list in self.independent_constraints():
            l.debug("... got %d constraints with %d variables", len(c_list), len(variables))

            s = self.blank_copy()
            s.add(c_list)
            results.append(s)
        return results

    #
    # Light functionality
    #

    def add(self, constraints):
        self.constraints += constraints
        for c in constraints:
            self.variables.update(c.variables)
        return constraints

    def simplify(self):
        to_simplify = [ c for c in self.constraints if not any(
            isinstance(a, SimplificationAvoidanceAnnotation) for a in c.annotations
        ) ]
        no_simplify = [ c for c in self.constraints if any(
            isinstance(a, SimplificationAvoidanceAnnotation) for a in c.annotations
        ) ]

        if len(to_simplify) == 0:
            return self.constraints

        simplified = simplify(And(*to_simplify)).split(['And']) #pylint:disable=no-member
        self.constraints = no_simplify + simplified
        return self.constraints

    #
    # Stuff that should be implemented by subclasses
    #

    def satisfiable(self, extra_constraints=(), exact=None):
        raise NotImplementedError("satisfiable() is not implemented")

    def batch_eval(self, e, n, extra_constraints=(), exact=None):
        raise NotImplementedError("batch_eval() is not implemented")

    def eval(self, e, n, extra_constraints=(), exact=None):
        raise NotImplementedError("eval() is not implemented")

    def min(self, e, extra_constraints=(), exact=None):
        raise NotImplementedError("min() is not implemented")

    def max(self, e, extra_constraints=(), exact=None):
        raise NotImplementedError("max() is not implemented")

    def solution(self, e, v, extra_constraints=(), exact=None):
        raise NotImplementedError("solution() is not implemented")

    def is_true(self, e, extra_constraints=(), exact=None):
        raise NotImplementedError("is_true() is not implemented")

    def is_false(self, e, extra_constraints=(), exact=None):
        raise NotImplementedError("is_false() is not implemented")

from ..ast.base import simplify
from ..ast.bool import And, Or
from ..annotation import SimplificationAvoidanceAnnotation
