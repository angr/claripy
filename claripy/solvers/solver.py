#!/usr/bin/env python

import logging
l = logging.getLogger("claripy.solvers.solver")

sat = 'sat'
unsat = 'unsat'

class Solver(object):
    def __init__(self, claripy):
        self._claripy = claripy
        self._finalized = None
        self._results = None
        self._constraints = None
        self._variables = None
        self._id = None

    #
    # Constraints
    #

    def add(self, *constraints, **kwargs):
        raise NotImplementedError()

    #
    # Solving
    #

    def check(self):
        raise NotImplementedError()

    def satisfiable(self):
        return self.check() == sat

    def any(self, expr, extra_constraints=None):
        return self.eval(expr, 1, extra_constraints)[0]

    def eval(self, expr, n, extra_constraints=None):
        raise NotImplementedError()

    def max(self, expr, extra_constraints=None):
        raise NotImplementedError()

    def min(self, expr, extra_constraints=None):
        raise NotImplementedError()

    #
    # Merging and splitting
    #

    def finalize(self):
        raise NotImplementedError()

    def branch(self):
        raise NotImplementedError()

    def merge(self, others, merge_flag, merge_values):
        raise NotImplementedError()

    def combine(self, others):
        combined = self._claripy.solver(self._claripy)
        combined.add(self._constraints)
        for o in others:
            combined.add(*o.constraints)
        return combined

    def split(self):
        raise NotImplementedError()
