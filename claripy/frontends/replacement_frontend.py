#!/usr/bin/env python

import weakref
import logging
l = logging.getLogger("claripy.frontends.full_frontend")

from .constrained_frontend import ConstrainedFrontend

class ReplacementFrontend(ConstrainedFrontend):
    def __init__(self, actual_frontend, replacements=None, replacement_cache=None, **kwargs):
        ConstrainedFrontend.__init__(self, **kwargs)
        self._actual_frontend = actual_frontend
        self._replacements = { } if replacements is None else replacements
        self._replacement_cache = weakref.WeakKeyDictionary() if replacement_cache is None else replacement_cache

    def add_replacement(self, old, new, invalidate_cache=False):
        if invalidate_cache:
            self._replacements = dict(self._replacements)
            self._replacement_cache = weakref.WeakKeyDictionary(self._replacement_cache)

        self._replacements[old.cache_key] = new
        self._replacement_cache[old.cache_key] = new

    def _replacement(self, old):
        if not isinstance(old, Base):
            return old

        if old.cache_key in self._replacement_cache:
            return self._replacement_cache[old.cache_key]
        else:
            new = old.replace_dict(self._replacement_cache)
            self._replacement_cache[old.cache_key] = new
            return new

    #
    # Storable support
    #

    def _blank_copy(self):
        return ReplacementFrontend(self._actual_frontend._blank_copy())

    def branch(self):
        return ReplacementFrontend(self._actual_frontend.branch(), replacements=self._replacements, replacement_cache=self._replacement_cache)

    def downsize(self):
        self._actual_frontend.downsize()
        self._replacement_cache.clear()

    def _ana_getstate(self):
        return self._replacements, self._actual_frontend, ConstrainedFrontend._ana_getstate(self)

    def _ana_setstate(self, s):
        self._replacements, self._actual_frontend, base_state = s
        ConstrainedFrontend._ana_setstate(base_state)
        self._replacement_cache = weakref.WeakKeyDictionary()

    #
    # Replacement solving
    #

    def _replace_list(self, lst):
        return tuple(self._replacement(c) for c in lst)

    def solve(self, extra_constraints=(), exact=None, cache=None):
        ecr = self._replace_list(extra_constraints)
        return self._actual_frontend.solve(extra_constraints=ecr, exact=exact, cache=cache)

    def eval(self, e, n, extra_constraints=(), exact=None, cache=None):
        er = self._replacement(e)
        ecr = self._replace_list(extra_constraints)
        return self._actual_frontend.eval(er, n, extra_constraints=ecr, exact=exact, cache=cache)

    def max(self, e, extra_constraints=(), exact=None, cache=None):
        er = self._replacement(e)
        ecr = self._replace_list(extra_constraints)
        return self._actual_frontend.max(er, extra_constraints=ecr, exact=exact, cache=cache)

    def min(self, e, extra_constraints=(), exact=None, cache=None):
        er = self._replacement(e)
        ecr = self._replace_list(extra_constraints)
        return self._actual_frontend.min(er, extra_constraints=ecr, exact=exact, cache=cache)

    def solution(self, e, v, extra_constraints=(), exact=None, cache=None):
        er = self._replacement(e)
        vr = self._replacement(v)
        ecr = self._replace_list(extra_constraints)
        return self._actual_frontend.solution(er, vr, extra_constraints=ecr, exact=exact, cache=cache)

    def add(self, constraints, **kwargs):
        cr = self._replace_list(constraints)
        return self._actual_frontend.add(cr, **kwargs)

    def _add_constraints(self, *args, **kwargs): #pylint:disable=unused-argument
        raise Exception("this should not be called")
    def _solve(self, *args, **kwargs): #pylint:disable=unused-argument
        raise Exception("this should not be called")
    def _eval(self, *args, **kwargs): #pylint:disable=unused-argument
        raise Exception("this should not be called")
    def _max(self, *args, **kwargs): #pylint:disable=unused-argument
        raise Exception("this should not be called")
    def _min(self, *args, **kwargs): #pylint:disable=unused-argument
        raise Exception("this should not be called")
    def _solution(self, *args, **kwargs): #pylint:disable=unused-argument
        raise Exception("this should not be called")

from ..ast.base import Base
