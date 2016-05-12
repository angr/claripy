#!/usr/bin/env python

import logging
l = logging.getLogger("claripy.frontends.frontend")

import sys
from ..frontend import Frontend

#pylint:disable=unidiomatic-typecheck

class CachingFrontend(Frontend):
    def __init__(self, cache=None):
        Frontend.__init__(self)

        self.result = None
        self._simplified = False
        self._cache = cache is not False

    #
    # Storable support
    #

    def _ana_getstate(self):
        if not self._simplified: self.simplify()
        return self.result, self._cache, Frontend._ana_getstate(self)

    def _ana_setstate(self, s):
        self.result, self._cache, frontend_state = s
        self._simplified = True
        Frontend._ana_setstate(self, frontend_state)

    def branch(self):
        s = self._blank_copy()
        s.result = self.result
        s._simplified = self._simplified
        return s

    def _blank_copy(self):
        return CachingFrontend(cache=self._cache)

    #
    # Constraint management
    #

    @staticmethod
    def _split_constraints(constraints):
        """
        Returns independent constraints, split from this Frontend's `constraints`.
        """

        splitted = [ ]
        for i in constraints:
            splitted.extend(i.split(['And']))

        l.debug("... splitted of size %d", len(splitted))

        variable_connections = { }
        constraint_connections = { }
        for n,s in enumerate(splitted):
            l.debug("... processing constraint with %d variables", len(s.variables))

            connected_variables = set(s.variables)
            connected_constraints = { n }

            if len(connected_variables) == 0:
                connected_variables.add('CONCRETE')

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
        return results

    def _filter_single_constraint(self, e_simp): #pylint:disable=no-self-use
        if not isinstance(e_simp, (Bool, bool)):
            l.warning("Frontend._constraint_filter got non-boolean from model_backend")
            raise ClaripyFrontendError()

        if self._eager_resolution('is_false', False, e_simp, use_result=False):
            raise UnsatError("expressions contain False")
        elif self._eager_resolution('is_true', False, e_simp, use_result=False):
            return None
        else:
            return e_simp

    def _constraint_filter(self, ec):
        fc = [ ]
        for e in ec if type(ec) in (list, tuple, set) else (ec,):
            #e_simp = self._claripy.simplify(e)
            c = self._filter_single_constraint(e)
            if c is not None:
                fc.append(c)

        return tuple(fc)

    #
    # Stuff that should be implemented by subclasses
    #

    def _add_constraints(self, constraints, invalidate_cache=True):
        raise NotImplementedError("_add_constraints() is not implemented")

    def _simplify(self):
        raise NotImplementedError("_simplify() is not implemented")

    def _solve(self, extra_constraints=(), exact=None, cache=None):
        raise NotImplementedError("_solve() is not implemented")

    def _eval(self, e, n, extra_constraints=(), exact=None, cache=None):
        raise NotImplementedError("_eval() is not implemented")

    def _batch_eval(self, exprs, n, extra_constraints=(), exact=None, cache=None):
        raise NotImplementedError("_batch_eval() is not implemented")

    def _min(self, e, extra_constraints=(), exact=None, cache=None):
        raise NotImplementedError("_min() is not implemented")

    def _max(self, e, extra_constraints=(), exact=None, cache=None):
        raise NotImplementedError("_max() is not implemented")

    def _solution(self, e, v, extra_constraints=(), exact=None, cache=None):
        raise NotImplementedError("_solution() is not implemented")

    def _is_true(self, e, extra_constraints=(), exact=None, cache=None):
        raise NotImplementedError("_is_true() is not implemented")

    def _is_false(self, e, extra_constraints=(), exact=None, cache=None):
        raise NotImplementedError("_is_false() is not implemented")

    def finalize(self):
        raise NotImplementedError("finalize() is not implemented")

    def merge(self, others, merge_flag, merge_values):
        raise NotImplementedError("merge() is not implemented")

    def combine(self, others):
        raise NotImplementedError("combine() is not implemented")

    def split(self):
        raise NotImplementedError("split() is not implemented")

    #
    # Caching
    #

    def _cache_eval(self, e, values, n=None, exact=None, cache=None):
        if exact is False or cache is False or not self._cache or self.result is None:
            return

        self.result.eval_cache[e.uuid] = self.result.eval_cache[e.uuid] | values if e.uuid in self.result.eval_cache else values
        if n is not None:
            self.result.eval_n[e.uuid] = max(n, self.result.eval_n[e.uuid]) if e.uuid in self.result.eval_n else n

    def _cache_max(self, e, m, exact=None, cache=None):
        if exact is False or cache is False or not self._cache or self.result is None:
            return

        self._cache_eval(e, {m}, exact=exact, cache=cache)
        self.result.max_cache[e.uuid] = min(self.result.max_cache.get(e, (2**e.length)-1), m)

    def _cache_min(self, e, m, exact=None, cache=None):
        if exact is False or cache is False or not self._cache or self.result is None:
            return

        self._cache_eval(e, {m}, exact=exact, cache=cache)
        self.result.min_cache[e.uuid] = max(self.result.min_cache.get(e, 0), m)

    #
    # Solving
    #

    def add(self, constraints, invalidate_cache=True):
        if type(constraints) not in (list, tuple):
            constraints = [ constraints ]

        if len(constraints) == 0:
            return [ ]

        try:
            to_add = self._constraint_filter(constraints)
        except UnsatError:
            self.result = UnsatResult()
            to_add = [ false ]

        if len(to_add) == 0:
            return [ ]

        for c in to_add:
            if not isinstance(c, Bool):
                raise ClaripyTypeError('constraint is not a boolean expression!')
            c.make_uuid()

        if self.result is not None and invalidate_cache:
            all_true = True
            for c in to_add:
                v = self._eager_resolution('eval', [None], c, 1)[0]
                if v is None:
                    all_true = False
                    break
                else:
                    all_true &= v
        else:
            all_true = False

        self._add_constraints(to_add, invalidate_cache=invalidate_cache)
        self._simplified = False

        if invalidate_cache and self.result is not None and self.result.sat:
            if all_true:
                new_result = SatResult()
                new_result.model.update(self.result.model)
                self.result = new_result
            else:
                self.result = None

        return to_add

    def simplify(self):
        if self._simplified:
            return

        s = self._simplify()
        self._simplified = True
        return s

    def solve(self, extra_constraints=(), exact=None, cache=None):
        l.debug("%s.solve() running with %d extra constraints...", self.__class__.__name__, len(extra_constraints))

        if self.result is not None:
            if not self.result.sat or len(extra_constraints) == 0:
                l.debug("... returning cached result (sat: %s)", self.result.sat)
                return self.result
        else:
            l.debug("... no cached result")

        try:
            extra_constraints = self._constraint_filter(extra_constraints)
        except UnsatError:
            l.debug("... returning unsat result due to false extra_constraints")
            return UnsatResult()

        l.debug("... conferring with the solver")
        r = self._solve(extra_constraints=extra_constraints, exact=exact, cache=cache)
        if exact is not False and cache is not False and (len(extra_constraints) == 0 or (self.result is None and r.sat)):
            l.debug("... caching result (sat: %s)", r.sat)
            self.result = r
        return r

    def satisfiable(self, extra_constraints=(), exact=None, cache=None):
        return self.solve(extra_constraints=extra_constraints, exact=exact, cache=cache).sat

    @staticmethod
    def _concrete_type_check(e):
        """
        Checks two things:

            1. Whether we can just return this value.
            2. Whether we can even process this value.

        Returns True if we don't have to pass this to any backends, False if we need
        to, and raises ClaripyValueError otherwise.
        """

        if isinstance(e, (int, long)):
            return True
        elif not isinstance(e, Base):
            raise ClaripyValueError("Expressions passed to min() MUST be Claripy ASTs (got %s)" % type(e))
        else:
            return False

    def eval_to_ast(self, e, n, extra_constraints=(), exact=None, cache=None):
        """
        Evaluates expression e, returning the results in the form of concrete ASTs.
        """

        return [ BVV(v, e.size()) for v in self.eval(e, n, extra_constraints=extra_constraints, exact=exact, cache=cache) ]

    def _eager_resolution(self, what, default, *args, **kwargs):
        for b in backends._eager_backends:
            try: return getattr(b, what)(*args, result=self.result if kwargs.pop('use_result', True) else None, **kwargs)
            except BackendError: pass
        return default

    def eval(self, e, n, extra_constraints=(), exact=None, cache=None):
        """
        Evaluates an expression, returning a tuple of n solutions.

        :param e:                   The expression
        :param n:                   The number of solutions to return
        :param extra_constraints:   Extra constraints to consider when performing the evaluation.
        :param exact:               Whether or not to perform an exact evaluation. Ignored by non-approximating
                                    backends.
        :param cache:               Whether or not to cache the results

        :returns:                   A tuple of python pritives representing results
        """

        if self._concrete_type_check(e): return (e,)

        extra_constraints = self._constraint_filter(extra_constraints)
        l.debug("Frontend.eval() for UUID %s with n=%d and %d extra_constraints", e.uuid, n, len(extra_constraints))

        # first, try evaluating through the eager backends
        try:
            eager_results = frozenset(self._eager_resolution('eval', (), e, n, extra_constraints=extra_constraints))
            if not e.symbolic and len(eager_results) > 0:
                return tuple(sorted(eager_results))
            self._cache_eval(e, eager_results, exact=exact, cache=cache)
        except UnsatError:
            # this can happen when the eager backend comes across an unsat extra condition
            # *while using the current model*. A new constraint solve could return a new,
            # sat model
            pass

        # then, check the cache
        if len(extra_constraints) == 0 and self.result is not None and e.uuid in self.result.eval_cache:
            cached_results = self.result.eval_cache[e.uuid]
            cached_n = self.result.eval_n.get(e.uuid, 0)
        else:
            cached_results = frozenset()
            cached_n = 0

        # if there's enough in the cache, return that
        if cached_n >= n or len(cached_results) < cached_n or len(cached_results) >= n:
            return tuple(sorted(cached_results))[:n]

        # try to make sure we don't get more of the same
        solver_extra_constraints = list(extra_constraints) + [e != v for v in cached_results]

        # if we still need more results, get them from the frontend
        try:
            n_lacking = n - len(cached_results)
            eval_results = frozenset(
                    self._eval(e, n_lacking, extra_constraints=solver_extra_constraints, exact=exact, cache=cache)
            )
            l.debug("... got %d more values", len(eval_results))
        except UnsatError:
            l.debug("... UNSAT")
            if len(cached_results) == 0:
                raise
            else:
                eval_results = frozenset()
        except BackendError:
            e_type, value, traceback = sys.exc_info()
            raise ClaripyFrontendError, "Backend error during eval: %s('%s')" % (str(e_type), str(value)), traceback

        # if, for some reason, we have no result object, make an approximate one
        if self.result is None:
            self.result = SatResult(approximation=True)

        # if there are less possible solutions than n (i.e., meaning we got all the solutions for e),
        # add constraints to help the solver out later
        # TODO: does this really help?
        all_results = cached_results | eval_results
        if len(extra_constraints) == 0 and len(all_results) < n:
            l.debug("... adding constraints for %d values for future speedup", len(all_results))
            self.add([Or(*[e == v for v in eval_results | cached_results])], invalidate_cache=False)

        # fix up the cache. If there were extra constraints, we can't assume that we got
        # all of the possible solutions, so we have to settle for a biggest-evaluated value
        # equal to the number of values we got
        self._cache_eval(e, all_results, n=n if len(extra_constraints) == 0 else None, exact=exact, cache=cache)

        # sort so the order of results is consistent when using pypy
        return tuple(sorted(all_results))

    def batch_eval(self, exprs, n, extra_constraints=(), exact=None, cache=None):

        def _formulate_results(all_exprs, symbolic_exprs, results):
            """
            Build a list of results with both concrete and symbolic expressions from a list of all expressions and
            results of symbolic expressions.

            :param all_exprs: All expressions, including both concrete and symbolic
            :param symbolic_exprs: A list of all symbolic expressions
            :param results: A list of all results for symbolic expressions
            :return: A list of tuples, where each tuple corresponds to a complete list of solutions to all expressions
            """

            # Offset of each expr expr in symbolic_exprs
            # None - concrete expr
            # int - offset in symbolic_exprs
            expr_offsets = [ ]

            symbolic_expr_pos = 0
            for expr in all_exprs:
                if symbolic_expr_pos < len(symbolic_exprs) and \
                                expr is symbolic_exprs[symbolic_expr_pos]:
                    expr_offsets.append(symbolic_expr_pos)
                    symbolic_expr_pos += 1
                else:
                    expr_offsets.append(None)

            formulated_results = [ ]
            for r in results:
                formulated_result = [ ]
                for i, offset in enumerate(expr_offsets):
                    if offset is None:
                        # concrete expr
                        formulated_result.append(all_exprs[i])
                    else:
                        # symbolic expr
                        formulated_result.append(r[offset])
                formulated_results.append(tuple(formulated_result))

            return formulated_results

        def _expr_from_results(exprs, results):
            """
            Generate a list of expressions based on the given expression list and result list to constrain the values of
            those expressions.

            :param exprs: A list of expressions
            :param results: A list of results for those expressions
            :return: A list of claripy expressions.
            """
            return [ Not(And(*[ ex == v for ex, v in zip(exprs, values) ])) for values in results ]

        symbolic_exprs = [ ]

        for ex in exprs:
            if not self._concrete_type_check(ex):
                symbolic_exprs.append(ex)

        if not symbolic_exprs:
            return [ exprs ]

        extra_constraints = self._constraint_filter(extra_constraints)
        l.debug("Frontend.batch_eval() for UUID %s with n=%d and %d extra_constraints",
                [ ex.uuid for ex in symbolic_exprs ],
                n,
                len(extra_constraints)
                )

        # first, try evaluating through the eager backends
        try:
            eager_results = frozenset(
                    self._eager_resolution('batch_eval', (), symbolic_exprs, n, extra_constraints=extra_constraints))
            if all([ not ex.symbolic for ex in symbolic_exprs ]) and len(eager_results) > 0:
                return _formulate_results(exprs, symbolic_exprs, eager_results)
        except UnsatError:
            # this can happen when the eager backend comes across an unsat extra condition
            # *while using the current model*. A new constraint solve could return a new,
            # sat model
            eager_results = [ ]

        # if there's enough from eager backends, return that
        if len(eager_results) >= n:
            return _formulate_results(exprs, symbolic_exprs, list(eager_results)[ : n])

        # try to make sure we don't get more of the same
        solver_extra_constraints = list(extra_constraints) + _expr_from_results(symbolic_exprs, eager_results)

        # if we still need more results, get them from the frontend
        try:
            n_lacking = n - len(eager_results)
            eval_results = frozenset(
                self._batch_eval(
                        symbolic_exprs, n_lacking, extra_constraints=solver_extra_constraints, exact=exact, cache=cache
                )
            )
            l.debug("... got %d more values", len(eval_results))
        except UnsatError:
            l.debug("... UNSAT")
            if len(eager_results) == 0:
                raise
            else:
                eval_results = frozenset()
        except BackendError:
            e_type, value, traceback = sys.exc_info()
            raise ClaripyFrontendError, "Backend error during eval: %s('%s')" % (str(e_type), str(value)), traceback

        # if, for some reason, we have no result object, make an approximate one
        if self.result is None:
            self.result = SatResult(approximation=True)

        all_results = eager_results | eval_results
        return _formulate_results(exprs, symbolic_exprs, all_results)

    def max(self, e, extra_constraints=(), exact=None, cache=None):
        if self._concrete_type_check(e): return e
        extra_constraints = self._constraint_filter(extra_constraints)

        # first, try evaluating through the eager backends
        v = self._eager_resolution('max', None, e, extra_constraints=extra_constraints, use_result=False)
        if v is not None:
            return v

        if len(extra_constraints) == 0 and self.result is not None and e.uuid in self.result.max_cache:
            #cached_max += 1
            return self.result.max_cache[e.uuid]

        m = self._max(e, extra_constraints=extra_constraints, exact=exact, cache=cache)
        if len(extra_constraints) == 0 and e.symbolic:
            self._cache_max(e, m, exact=exact, cache=cache)
            self.add([ULE(e, m)], invalidate_cache=False)
        return m

    def min(self, e, extra_constraints=(), exact=None, cache=None):
        if self._concrete_type_check(e): return e
        extra_constraints = self._constraint_filter(extra_constraints)

        # first, try evaluating through the eager backends
        v = self._eager_resolution('min', None, e, extra_constraints=extra_constraints, use_result=False)
        if v is not None:
            return v

        if len(extra_constraints) == 0 and self.result is not None and e.uuid in self.result.min_cache:
            #cached_min += 1
            return self.result.min_cache[e.uuid]

        m = self._min(e, extra_constraints=extra_constraints, exact=exact, cache=cache)
        if len(extra_constraints) == 0 and e.symbolic:
            self._cache_min(e, m, exact=exact, cache=cache)
            self.add([UGE(e, m)], invalidate_cache=False)
        return m

    def solution(self, e, v, extra_constraints=(), exact=None, cache=None):
        try:
            extra_constraints = self._constraint_filter(extra_constraints)
        except UnsatError:
            return False

        if self._concrete_type_check(e) and self._concrete_type_check(v):
            return e == v
        eager_solution = self._eager_resolution('solution', None, e, v)
        if eager_solution is not None:
            return eager_solution

        b = self._solution(e, v, extra_constraints=extra_constraints, exact=exact, cache=cache)
        if b is False and len(extra_constraints) == 0 and e.symbolic:
            self.add([e != v], invalidate_cache=False)

        # add these results to the cache
        if self.result is not None and b is True:
            if isinstance(e, Base) and e.symbolic and not isinstance(v, Base):
                self._cache_eval(e, frozenset({v}), exact=exact, cache=cache)
            if isinstance(v, Base) and v.symbolic and not isinstance(e, Base):
                self._cache_eval(v, frozenset({e}), exact=exact, cache=cache)

        return b

    def is_true(self, e, extra_constraints=(), exact=None, cache=None):
        if self._concrete_type_check(e):
            return e is True

        if not isinstance(e, Bool):
            raise ClaripyValueError("got a non-Boolean expression in Frontend.is_true()")

        eager_solution = self._eager_resolution('is_true', None, e)
        if eager_solution is True:
            return eager_solution

        try:
            b = self._is_true(e, extra_constraints=extra_constraints, exact=exact, cache=cache)
            if b is True and len(extra_constraints) == 0 and e.symbolic:
                self.add([e == True], invalidate_cache=False)
            return b
        except ClaripyFrontendError:
            return False

    def is_false(self, e, extra_constraints=(), exact=None, cache=None):
        if self._concrete_type_check(e):
            return e is False

        if not isinstance(e, Bool):
            raise ClaripyValueError("got a non-Boolean expression in Frontend.is_false()")

        eager_solution = self._eager_resolution('is_false', None, e)
        if eager_solution is True:
            return eager_solution

        try:
            b = self._is_false(e, extra_constraints=extra_constraints, exact=exact, cache=cache)
            if b is True and len(extra_constraints) == 0 and e.symbolic:
                self.add([e == False], invalidate_cache=False)
            return b
        except ClaripyFrontendError:
            return False

    #
    # Serialization and such.
    #

    def downsize(self): #pylint:disable=R0201
        if self.result is not None:
            self.result.downsize()

from ..result import UnsatResult, SatResult
from ..errors import UnsatError, BackendError, ClaripyFrontendError, ClaripyTypeError, ClaripyValueError
from ..backend_manager import backends
from ..ast.base import Base
from ..ast.bool import false, Bool, And, Or, Not
from ..ast.bv import UGE, ULE, BVV
