#!/usr/bin/env python

import logging
import numbers
import weakref

l = logging.getLogger("claripy.frontends.replacement_frontend")

from .constrained_frontend import ConstrainedFrontend

class ReplacementFrontend(ConstrainedFrontend):
    def __init__(self, actual_frontend, allow_symbolic=None, replacements=None, replacement_cache=None, unsafe_replacement=None, complex_auto_replace=None, auto_replace=None, replace_constraints=None, **kwargs):
        super(ReplacementFrontend, self).__init__(**kwargs)
        self._actual_frontend = actual_frontend
        self._allow_symbolic = True if allow_symbolic is None else allow_symbolic
        self._auto_replace = True if auto_replace is None else auto_replace
        self._complex_auto_replace = False if complex_auto_replace is None else complex_auto_replace
        self._replace_constraints = False if replace_constraints is None else replace_constraints
        self._unsafe_replacement = False if unsafe_replacement is None else unsafe_replacement
        self._replacements = {} if replacements is None else replacements
        self._replacement_cache = weakref.WeakKeyDictionary() if replacement_cache is None else replacement_cache

        self._validation_frontend = None

    def _blank_copy(self, c):
        super(ReplacementFrontend, self)._blank_copy(c)
        c._actual_frontend = self._actual_frontend.blank_copy()
        c._allow_symbolic = self._allow_symbolic
        c._auto_replace = self._auto_replace
        c._complex_auto_replace = self._complex_auto_replace
        c._replace_constraints = self._replace_constraints
        c._unsafe_replacement = self._unsafe_replacement
        c._replacements = {}
        c._replacement_cache = weakref.WeakKeyDictionary()

        if self._validation_frontend is not None:
            c._validation_frontend = self._validation_frontend.blank_copy()
        else:
            c._validation_frontend = None

    def _copy(self, c):
        super(ReplacementFrontend, self)._copy(c)
        self._actual_frontend._copy(c._actual_frontend)
        if self._validation_frontend is not None:
            self._validation_frontend._copy(c._validation_frontend)

        c._replacements = self._replacements
        c._replacement_cache = self._replacement_cache

    #
    # Replacements
    #

    def add_replacement(self, old, new, invalidate_cache=True, replace=True, promote=True):
        if not isinstance(old, Base):
            return

        if old is new:
            return

        if not replace and old.cache_key in self._replacements:
            return

        if not promote and old.cache_key in self._replacement_cache:
            return

        if not isinstance(new, Base):
            if isinstance(new, bool):
                new = BoolV(new)
            elif isinstance(new, numbers.Number):
                new = BVV(new, old.length)
            else:
                return

        if invalidate_cache:
            self._replacements = dict(self._replacements)
            self._replacement_cache = weakref.WeakKeyDictionary(self._replacements)

        self._replacements[old.cache_key] = new
        self._replacement_cache[old.cache_key] = new

    def remove_replacements(self, old_entries):
        self._replacements = {k: v for k, v in self._replacements.items() if k not in old_entries}
        self._replacement_cache = weakref.WeakKeyDictionary(self._replacements)

    def clear_replacements(self):
        self._replacements = dict()
        self._replacement_cache = weakref.WeakKeyDictionary(self._replacements)

    def _replacement(self, old):
        # depressing hack
        try:
            if not self._replacement_cache:
                return old
        except RuntimeError:
            if not self._replacement_cache:
                return old

        if not isinstance(old, Base):
            return old

        try:
            return self._replacement_cache[old.cache_key]
        except KeyError:
            # not found in the cache
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

    def downsize(self):
        self._actual_frontend.downsize()
        self._replacement_cache.clear()

    def __getstate__(self):
        return (
            self._allow_symbolic,
            self._unsafe_replacement,
            self._complex_auto_replace,
            self._auto_replace,
            self._replace_constraints,
            self._replacements,
            self._actual_frontend,
            self._validation_frontend,
            super().__getstate__()
        )

    def __setstate__(self, s):
        (
            self._allow_symbolic,
            self._unsafe_replacement,
            self._complex_auto_replace,
            self._auto_replace,
            self._replace_constraints,
            self._replacements,
            self._actual_frontend,
            self._validation_frontend,
            base_state
        ) = s

        super().__setstate__(base_state)
        self._replacement_cache = weakref.WeakKeyDictionary(self._replacements)

    #
    # Replacement solving
    #

    def _replace_list(self, lst):
        return tuple(self._replacement(c) for c in lst)

    def eval(self, e, n, extra_constraints=(), exact=None):
        er = self._replacement(e)
        ecr = self._replace_list(extra_constraints)
        r = self._actual_frontend.eval(er, n, extra_constraints=ecr, exact=exact)
        if self._unsafe_replacement: self._add_solve_result(e, er, r[0])
        return r

    def batch_eval(self, exprs, n, extra_constraints=(), exact=None):
        er = self._replace_list(exprs)
        ecr = self._replace_list(extra_constraints)
        r = self._actual_frontend.batch_eval(er, n, extra_constraints=ecr, exact=exact)
        if self._unsafe_replacement:
            for i, original in enumerate(exprs):
                self._add_solve_result(original, er[i], r[0][i])
        return r

    def max(self, e, extra_constraints=(), exact=None):
        er = self._replacement(e)
        ecr = self._replace_list(extra_constraints)
        r = self._actual_frontend.max(er, extra_constraints=ecr, exact=exact)
        if self._unsafe_replacement: self._add_solve_result(e, er, r)
        return r

    def min(self, e, extra_constraints=(), exact=None):
        er = self._replacement(e)
        ecr = self._replace_list(extra_constraints)
        r = self._actual_frontend.min(er, extra_constraints=ecr, exact=exact)
        if self._unsafe_replacement: self._add_solve_result(e, er, r)
        return r

    def solution(self, e, v, extra_constraints=(), exact=None):
        er = self._replacement(e)
        vr = self._replacement(v)
        ecr = self._replace_list(extra_constraints)
        r = self._actual_frontend.solution(er, vr, extra_constraints=ecr, exact=exact)
        if self._unsafe_replacement and r and (not isinstance(vr, Base) or not vr.symbolic):
            self._add_solve_result(e, er, vr)
        return r

    def is_true(self, e, extra_constraints=(), exact=None):
        er = self._replacement(e)
        ecr = self._replace_list(extra_constraints)
        return self._actual_frontend.is_true(er, extra_constraints=ecr, exact=exact)

    def is_false(self, e, extra_constraints=(), exact=None):
        er = self._replacement(e)
        ecr = self._replace_list(extra_constraints)
        return self._actual_frontend.is_false(er, extra_constraints=ecr, exact=exact)

    def satisfiable(self, extra_constraints=(), exact=None):
        ecr = self._replace_list(extra_constraints)
        return self._actual_frontend.satisfiable(extra_constraints=ecr, exact=exact)

    def _concrete_value(self, e):
        c = super(ReplacementFrontend, self)._concrete_value(e)
        if c is not None: return c

        cr = self._replacement(e)
        for b in backends._eager_backends:
            try: return b.eval(cr, 1)[0]
            except BackendError: pass
        return None

    def _concrete_constraint(self, e):
        c = super(ReplacementFrontend, self)._concrete_value(e)
        if c is not None: return c

        #if er.is_false():
        #   raise UnsatError("Replacement frontend received False constraint after replacement.")
        if self._replace_constraints:
            er = self._replacement(e)
            return super(ReplacementFrontend, self)._concrete_constraint(er)
        else:
            return super(ReplacementFrontend, self)._concrete_constraint(e)

    def add(self, constraints, **kwargs):
        if self._auto_replace:
            for c in constraints:
                # the badass thing here would be to use the *replaced* constraint, but
                # we don't currently support chains of replacements, so we'll do a
                # less effective flat-replacement with the original constraint
                # rc = self._replacement(c)
                rc = c
                if not isinstance(rc, Base) or not rc.symbolic:
                    continue

                if not self._complex_auto_replace:
                    if rc.op == 'Not':
                        self.add_replacement(c.args[0], false, replace=False, promote=True, invalidate_cache=True)
                    elif rc.op == '__eq__' and rc.args[0].symbolic ^ rc.args[1].symbolic:
                        old, new = rc.args if rc.args[0].symbolic else rc.args[::-1]
                        self.add_replacement(old, new, replace=False, promote=True, invalidate_cache=True)
                else:
                    satisfiable, replacements = Balancer(backends.vsa, rc, validation_frontend=self._validation_frontend).compat_ret
                    if not satisfiable:
                        self.add_replacement(rc, false)
                    for old, new in replacements:
                        if old.cardinality == 1:
                            continue

                        rold = self._replacement(old)
                        if rold.cardinality == 1:
                            continue

                        self.add_replacement(old, rold.intersection(new))

        added = super(ReplacementFrontend, self).add(constraints, **kwargs)
        cr = self._replace_list(added)
        if not self._allow_symbolic and any(c.symbolic for c in cr):
            raise ClaripyFrontendError(
                "symbolic constraints made it into ReplacementFrontend with allow_symbolic=False")
        self._actual_frontend.add(cr, **kwargs)

        return added


from ..ast.base import Base
from ..ast.bv import BVV
from ..ast.bool import BoolV, false
from ..errors import ClaripyFrontendError, BackendError
from ..balancer import Balancer
from ..backend_manager import backends
