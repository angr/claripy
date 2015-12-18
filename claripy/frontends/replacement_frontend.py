#!/usr/bin/env python

import weakref
import logging
l = logging.getLogger("claripy.frontends.full_frontend")

from .constrained_frontend import ConstrainedFrontend

class ReplacementFrontend(ConstrainedFrontend):
    def __init__(self, actual_frontend, allow_symbolic=None, replacements=None, replacement_cache=None, unsafe_replacement=None, auto_replace=None, replace_constraints=None, **kwargs):
        kwargs['cache'] = kwargs.get('cache', False)
        ConstrainedFrontend.__init__(self, **kwargs)
        self._actual_frontend = actual_frontend
        self._allow_symbolic = True if allow_symbolic is None else allow_symbolic
        self._auto_replace = True if auto_replace is None else auto_replace
        self._replace_constraints = False if replace_constraints is None else replace_constraints
        self._unsafe_replacement = False if unsafe_replacement is None else unsafe_replacement
        self._replacements = { } if replacements is None else replacements
        self._replacement_cache = weakref.WeakKeyDictionary() if replacement_cache is None else replacement_cache

    def add_replacement(self, old, new, invalidate_cache=True, replace=True):
        if not isinstance(old, Base):
            return

        if not replace and old in self._replacements:
            return

        if not isinstance(new, Base):
            if not isinstance(new, (int, long)):
                return
            new = BVV(new, old.length)

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
            if new is not old:
                self._replacement_cache[old.cache_key] = new
            return new

    def _add_solve_result(self, e, er, r):
        if not self._auto_replace:
            return
        if not isinstance(e, Base) or not e.symbolic:
            return
        if er.symbolic:
            return
        self.add_replacement(e, r, invalidate_cache=False)


    #
    # Storable support
    #

    def _blank_copy(self):
        s = ReplacementFrontend(self._actual_frontend._blank_copy())
        s._auto_replace = self._auto_replace
        s._replace_constraints = self._replace_constraints
        s._unsafe_replacement = self._unsafe_replacement
        s._allow_symbolic = self._allow_symbolic
        return s

    def branch(self):
        s = ConstrainedFrontend.branch(self)
        s._action_frontend = self._actual_frontend.branch()
        s._replacements = self._replacements
        s._replacement_cache = self._replacement_cache
        return s

    def downsize(self):
        self._actual_frontend.downsize()
        self._replacement_cache.clear()

    def _ana_getstate(self):
        return self._replacements, self._actual_frontend, ConstrainedFrontend._ana_getstate(self)

    def _ana_setstate(self, s):
        self._replacements, self._actual_frontend, base_state = s
        ConstrainedFrontend._ana_setstate(self, base_state)
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
        r = self._actual_frontend.eval(er, n, extra_constraints=ecr, exact=exact, cache=cache)
        if self._unsafe_replacement: self._add_solve_result(e, er, r[0])
        return r

    def batch_eval(self, exprs, n, extra_constraints=(), exact=None, cache=None):
        er = self._replace_list(exprs)
        ecr = self._replace_list(extra_constraints)
        r = self._actual_frontend.batch_eval(er, n, extra_constraints=ecr, exact=exact, cache=cache)
        if self._unsafe_replacement:
            for i, original in enumerate(exprs):
                self._add_solve_result(original, er[i], r[0][i])
        return r

    def max(self, e, extra_constraints=(), exact=None, cache=None):
        er = self._replacement(e)
        ecr = self._replace_list(extra_constraints)
        r = self._actual_frontend.max(er, extra_constraints=ecr, exact=exact, cache=cache)
        if self._unsafe_replacement: self._add_solve_result(e, er, r)
        return r

    def min(self, e, extra_constraints=(), exact=None, cache=None):
        er = self._replacement(e)
        ecr = self._replace_list(extra_constraints)
        r = self._actual_frontend.min(er, extra_constraints=ecr, exact=exact, cache=cache)
        if self._unsafe_replacement: self._add_solve_result(e, er, r)
        return r

    def solution(self, e, v, extra_constraints=(), exact=None, cache=None):
        er = self._replacement(e)
        vr = self._replacement(v)
        ecr = self._replace_list(extra_constraints)
        r = self._actual_frontend.solution(er, vr, extra_constraints=ecr, exact=exact, cache=cache)
        if self._unsafe_replacement and r and (not isinstance(vr, Base) or not vr.symbolic):
            self._add_solve_result(e, er, vr)
        return r

    def is_true(self, e, extra_constraints=(), exact=None, cache=None):
        er = self._replacement(e)
        ecr = self._replace_list(extra_constraints)
        return self._actual_frontend.is_true(er, extra_constraints=ecr, exact=exact, cache=cache)

    def is_false(self, e, extra_constraints=(), exact=None, cache=None):
        er = self._replacement(e)
        ecr = self._replace_list(extra_constraints)
        return self._actual_frontend.is_false(er, extra_constraints=ecr, exact=exact, cache=cache)

    def satisfiable(self, extra_constraints=(), exact=None, cache=None):
        ecr = self._replace_list(extra_constraints)
        return self._actual_frontend.satisfiable(extra_constraints=ecr, exact=exact, cache=cache)

    def _filter_single_constraint(self, e):
        if self._replace_constraints:
            er = self._replacement(e)
            return super(ReplacementFrontend, self)._filter_single_constraint(er)
        else:
            return super(ReplacementFrontend, self)._filter_single_constraint(e)

    def _add_constraints(self, constraints, **kwargs):
        for c in constraints:
            if self._auto_replace and isinstance(c, Base) and c.op == '__eq__' and isinstance(c.args[0], Base) and isinstance(c.args[1], Base):
                #print c; import ipdb; ipdb.set_trace()
                if c.args[0].symbolic ^ c.args[1].symbolic:
                    if c.args[0].cache_key not in self._replacements and c.args[0].cache_key not in self._replacement_cache:
                        self.add_replacement(c.args[0], c.args[1], invalidate_cache=True)
                    elif c.args[1].cache_key not in self._replacements and c.args[1].cache_key not in self._replacement_cache:
                        self.add_replacement(c.args[1], c.args[0], invalidate_cache=True)

        ConstrainedFrontend._add_constraints(self, constraints, **kwargs)

        cr = self._replace_list(constraints)
        if not self._allow_symbolic and any(c.symbolic for c in cr):
            raise ClaripyFrontendError("symbolic constraints made it into ReplacementFrontend with allow_symbolic=False")
        return self._actual_frontend.add(cr, **kwargs)

    #def _add_constraints(self, *args, **kwargs): #pylint:disable=unused-argument
    #   raise Exception("this should not be called")
    def _solve(self, *args, **kwargs): #pylint:disable=unused-argument
        raise Exception("this should not be called")
    def _eval(self, *args, **kwargs): #pylint:disable=unused-argument
        raise Exception("this should not be called")
    def _batch_eval(self, *args, **kwargs): #pylint:disable=unused-argument
        raise Exception("this should not be called")
    def _max(self, *args, **kwargs): #pylint:disable=unused-argument
        raise Exception("this should not be called")
    def _min(self, *args, **kwargs): #pylint:disable=unused-argument
        raise Exception("this should not be called")
    def _solution(self, *args, **kwargs): #pylint:disable=unused-argument
        raise Exception("this should not be called")
    def _is_true(self, *args, **kwargs): #pylint:disable=unused-argument
        raise Exception("this should not be called")
    def _is_false(self, *args, **kwargs): #pylint:disable=unused-argument
        raise Exception("this should not be called")

from ..ast.base import Base
from ..ast.bv import BVV
from ..errors import ClaripyFrontendError
