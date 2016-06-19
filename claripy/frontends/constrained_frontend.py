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
        self._simplified = False

    def _blank_copy(self, c):
        super(ConstrainedFrontend, self)._blank_copy(c)
        c.constraints = []
        c.variables = set()
        c._finalized = False
        c._simplified = False

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
    # Solving
    #

    #def batch_eval(self, exprs, n, extra_constraints=(), exact=None):

    #    def _formulate_results(all_exprs, symbolic_exprs, results):
    #        """
    #        Build a list of results with both concrete and symbolic expressions from a list of all expressions and
    #        results of symbolic expressions.

    #        :param all_exprs: All expressions, including both concrete and symbolic
    #        :param symbolic_exprs: A list of all symbolic expressions
    #        :param results: A list of all results for symbolic expressions
    #        :return: A list of tuples, where each tuple corresponds to a complete list of solutions to all expressions
    #        """

    #        # Offset of each expr expr in symbolic_exprs
    #        # None - concrete expr
    #        # int - offset in symbolic_exprs
    #        expr_offsets = [ ]

    #        symbolic_expr_pos = 0
    #        for expr in all_exprs:
    #            if symbolic_expr_pos < len(symbolic_exprs) and \
    #                            expr is symbolic_exprs[symbolic_expr_pos]:
    #                expr_offsets.append(symbolic_expr_pos)
    #                symbolic_expr_pos += 1
    #            else:
    #                expr_offsets.append(None)

    #        formulated_results = [ ]
    #        for r in results:
    #            formulated_result = [ ]
    #            for i, offset in enumerate(expr_offsets):
    #                if offset is None:
    #                    # concrete expr
    #                    formulated_result.append(all_exprs[i])
    #                else:
    #                    # symbolic expr
    #                    formulated_result.append(r[offset])
    #            formulated_results.append(tuple(formulated_result))

    #        return formulated_results

    #    def _expr_from_results(exprs, results):
    #        """
    #        Generate a list of expressions based on the given expression list and result list to constrain the values of
    #        those expressions.

    #        :param exprs: A list of expressions
    #        :param results: A list of results for those expressions
    #        :return: A list of claripy expressions.
    #        """
    #        return [ Not(And(*[ ex == v for ex, v in zip(exprs, values) ])) for values in results ]

    #    symbolic_exprs = [ ]

    #    for ex in exprs:
    #        if not self._concrete_type_check(ex):
    #            symbolic_exprs.append(ex)

    #    if not symbolic_exprs:
    #        return [ exprs ]

    #    extra_constraints = self._constraint_filter(extra_constraints)
    #    l.debug("Frontend.batch_eval() for UUID %s with n=%d and %d extra_constraints",
    #            [ ex.uuid for ex in symbolic_exprs ],
    #            n,
    #            len(extra_constraints)
    #            )

    #    # first, try evaluating through the eager backends
    #    try:
    #        eager_results = frozenset(
    #                self._eager_resolution('batch_eval', (), symbolic_exprs, n, extra_constraints=extra_constraints))
    #        if all([ not ex.symbolic for ex in symbolic_exprs ]) and len(eager_results) > 0:
    #            return _formulate_results(exprs, symbolic_exprs, eager_results)
    #    except UnsatError:
    #        # this can happen when the eager backend comes across an unsat extra condition
    #        # *while using the current model*. A new constraint solve could return a new,
    #        # sat model
    #        eager_results = [ ]

    #    # if there's enough from eager backends, return that
    #    if len(eager_results) >= n:
    #        return _formulate_results(exprs, symbolic_exprs, list(eager_results)[ : n])

    #    # try to make sure we don't get more of the same
    #    solver_extra_constraints = list(extra_constraints) + _expr_from_results(symbolic_exprs, eager_results)

    #    # if we still need more results, get them from the frontend
    #    try:
    #        n_lacking = n - len(eager_results)
    #        eval_results = frozenset(
    #            self._batch_eval(
    #                    symbolic_exprs, n_lacking, extra_constraints=solver_extra_constraints, exact=exact, cache=cache
    #            )
    #        )
    #        l.debug("... got %d more values", len(eval_results))
    #    except UnsatError:
    #        l.debug("... UNSAT")
    #        if len(eager_results) == 0:
    #            raise
    #        else:
    #            eval_results = frozenset()
    #    except BackendError:
    #        e_type, value, traceback = sys.exc_info()
    #        raise ClaripyFrontendError, "Backend error during eval: %s('%s')" % (str(e_type), str(value)), traceback

    #    # if, for some reason, we have no result object, make an approximate one
    #    if self.result is None:
    #        self.result = SatResult(approximation=True)

    #    all_results = eager_results | eval_results
    #    return _formulate_results(exprs, symbolic_exprs, all_results)

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

    def merge(self, others, merge_flag, merge_values):
        merged = self.blank_copy()
        merged._simplified = False
        options = []

        for s, v in zip([self] + others, merge_values):
            options.append(And(*([merge_flag == v] + s.constraints)))
        merged.add([Or(*options)])

        return False, merged

    def combine(self, others):
        combined = self.blank_copy()
        combined._simplified = False

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
            s._simplified = False
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
        if self._simplified or len(self.constraints) == 0:
            return [ ]

        self.constraints = [simplify(And(*self.constraints))]

        # generate UUIDs for every constraint
        for c in self.constraints:
            if isinstance(c, Base):
                c.make_uuid() #pylint:disable=no-member

        self._simplified = True
        return self.constraints

    def satisfiable(self, extra_constraints=(), exact=None):
        return self.solve(extra_constraints=extra_constraints, exact=exact).sat

    #
    # Stuff that should be implemented by subclasses
    #

    def solve(self, extra_constraints=(), exact=None):
        raise NotImplementedError("solve() is not implemented")

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

from ..ast.base import Base, simplify
from ..ast.bool import And, Or
from ..ast.bv import BVV
