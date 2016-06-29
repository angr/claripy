#!/usr/bin/env python

import logging
l = logging.getLogger("claripy.frontends.frontend")

import ana

class Frontend(ana.Storable):
    def __init__(self):
        pass

    def branch(self):
        c = self.blank_copy()
        self._copy(c)
        return c

    def blank_copy(self):
        c = self.__class__.__new__(self.__class__)
        self._blank_copy(c)
        return c

    def _blank_copy(self, c): #pylint:disable=no-self-use,unused-argument
        return

    def _copy(self, c): #pylint:disable=no-self-use,unused-argument
        return

    #
    # Storable support
    #

    @property
    def uuid(self):
        return self.ana_uuid

    def _ana_getstate(self):
        return None

    def _ana_setstate(self, s):
        pass

    #
    # Stuff that should be implemented by subclasses
    #

    def eval_to_ast(self, e, n, extra_constraints=(), exact=None):
        """
        Evaluates expression e, returning the results in the form of concrete ASTs.
        """
        return [ ast.bv.BVV(v, e.size()) for v in self.eval(e, n, extra_constraints=extra_constraints, exact=exact) ]


    def finalize(self):
        raise NotImplementedError("finalize() is not implemented")

    def merge(self, others, merge_conditions):
        raise NotImplementedError("merge() is not implemented")

    def combine(self, others):
        raise NotImplementedError("combine() is not implemented")

    def split(self):
        raise NotImplementedError("split() is not implemented")

    def add(self, constraints):
        raise NotImplementedError()

    def simplify(self):
        raise NotImplementedError()

    def satisfiable(self, extra_constraints=(), exact=None):
        raise NotImplementedError()

    def eval(self, e, n, extra_constraints=(), exact=None):
        raise NotImplementedError()

    def batch_eval(self, exprs, n, extra_constraints=(), exact=None):
        raise NotImplementedError()

    def max(self, e, extra_constraints=(), exact=None):
        raise NotImplementedError()

    def min(self, e, extra_constraints=(), exact=None):
        raise NotImplementedError()

    def solution(self, e, v, extra_constraints=(), exact=None):
        raise NotImplementedError()

    def is_true(self, e, extra_constraints=(), exact=None):
        raise NotImplementedError()

    def is_false(self, e, extra_constraints=(), exact=None):
        raise NotImplementedError()

    def downsize(self): #pylint:disable=no-self-use
        pass

    #
    # Some utility functions
    #

    def _concrete_value(self, e): #pylint:disable=no-self-use
        if isinstance(e, (int, long, bool, float)):
            return e
        else:
            return None
    _concrete_constraint = _concrete_value

    def _constraint_filter(self, c): #pylint:disable=no-self-use
        return c

    @staticmethod
    def _split_constraints(constraints, concrete=True):
        """
        Returns independent constraints, split from this Frontend's `constraints`.
        """

        splitted = [ ]
        for i in constraints:
            splitted.extend(i.split(['And']))

        l.debug("... splitted of size %d", len(splitted))

        concrete_constraints = [ ]
        variable_connections = { }
        constraint_connections = { }
        for n,s in enumerate(splitted):
            l.debug("... processing constraint with %d variables", len(s.variables))

            connected_variables = set(s.variables)
            connected_constraints = { n }

            if len(connected_variables) == 0:
                concrete_constraints.append(s)

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

        if concrete and len(concrete_constraints) > 0:
            results.append(({ 'CONCRETE' }, concrete_constraints))

        return results

from . import ast
