#!/usr/bin/env python

import logging
l = logging.getLogger("claripy.frontends.frontend")

import ana

class Frontend(ana.Storable):
    def __init__(self):
        pass

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

    def branch(self):
        return self._blank_copy()

    def _blank_copy(self): #pylint:disable=no-self-use
        return Frontend()

    #
    # Stuff that should be implemented by subclasses
    #

    def finalize(self):
        raise NotImplementedError("finalize() is not implemented")

    def merge(self, others, merge_flag, merge_values):
        raise NotImplementedError("merge() is not implemented")

    def combine(self, others):
        raise NotImplementedError("combine() is not implemented")

    def split(self):
        raise NotImplementedError("split() is not implemented")

    def add(self, constraints, invalidate_cache=True):
        raise NotImplementedError()

    def simplify(self):
        raise NotImplementedError()

    def solve(self, extra_constraints=(), exact=None, cache=None):
        raise NotImplementedError()

    def satisfiable(self, extra_constraints=(), exact=None, cache=None):
        raise NotImplementedError()

    def eval_to_ast(self, e, n, extra_constraints=(), exact=None, cache=None):
        raise NotImplementedError()

    def eval(self, e, n, extra_constraints=(), exact=None, cache=None):
        raise NotImplementedError()

    def batch_eval(self, exprs, n, extra_constraints=(), exact=None, cache=None):
        raise NotImplementedError()

    def max(self, e, extra_constraints=(), exact=None, cache=None):
        raise NotImplementedError()

    def min(self, e, extra_constraints=(), exact=None, cache=None):
        raise NotImplementedError()

    def solution(self, e, v, extra_constraints=(), exact=None, cache=None):
        raise NotImplementedError()

    def is_true(self, e, extra_constraints=(), exact=None, cache=None):
        raise NotImplementedError()

    def is_false(self, e, extra_constraints=(), exact=None, cache=None):
        raise NotImplementedError()

    def downsize(self):
        raise NotImplementedError()
