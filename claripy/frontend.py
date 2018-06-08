#!/usr/bin/env python

import logging
import numbers

import ana

l = logging.getLogger("claripy.frontends.frontend")


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

    def merge(self, others, merge_conditions, common_ancestor=None):
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
        if isinstance(e, numbers.Number):
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

        tree = {} # union-find data structure
        concrete_constraints = []
        rooted_constraints = {} # map from union-find roots to constraint lists

        def find(var):
            out = var
            while out in tree:
                out = tree[out]
            if out != var: # cache result
                tree[var] = out
            return out

        def union(var1, var2):
            root1 = find(var1)
            root2 = find(var2)
            if root1 != root2:
                tree[root1] = root2

        for s in splitted:
            if not s.symbolic:
                continue

            all_v = iter(s.variables)
            v_0 = next(all_v)

            for v in all_v:
                union(v_0, v)

        for s in splitted:
            if not s.symbolic:
                concrete_constraints.append(s)
                continue

            v = find(next(iter(s.variables)))
            if v not in rooted_constraints:
                rooted_constraints[v] = [s]
            else:
                rooted_constraints[v].append(s)

        results = [(frozenset.union(*[s.variables for s in cset]), cset) for cset in rooted_constraints.itervalues()]

        if concrete and len(concrete_constraints) > 0:
            results.append(({ 'CONCRETE' }, concrete_constraints))

        return results

from . import ast
