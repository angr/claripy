from __future__ import annotations

from numbers import Number

from claripy.ast.bvset import BoolSet, BVSet
from claripy.backends.backend import Backend


class BackendVSA(Backend):
    """BackendVSA is a backend that uses VSA (Value Set Analysis) to represent
    and reason about values.
    """

    def handles(self, expr):
        return isinstance(expr, Number | BoolSet | BVSet)

    def convert(self, expr):
        return expr

    def simplify(self, expr):
        return expr

    def is_true(self, e, extra_constraints=(), solver=None, model_callback=None):  # pylint:disable=unused-argument
        return isinstance(e, BoolSet) and e.is_true()

    def is_false(self, e, extra_constraints=(), solver=None, model_callback=None):  # pylint:disable=unused-argument
        return isinstance(e, BoolSet) and e.is_false()

    def has_true(self, e, extra_constraints=(), solver=None, model_callback=None):
        return isinstance(e, BoolSet) and e.has_true()

    def has_false(self, e, extra_constraints=(), solver=None, model_callback=None):
        return isinstance(e, BoolSet) and e.has_false()

    def eval(self, expr, n, extra_constraints=(), solver=None, model_callback=None):
        return expr.eval(n)

    def min(self, expr, extra_constraints=(), solver=None, model_callback=None):
        return expr.min()

    def max(self, expr, extra_constraints=(), solver=None, model_callback=None):
        return expr.max()

    def solution(self, expr, v, extra_constraints=(), solver=None, model_callback=None):
        return expr.solution(v)

    def cardinality(self, a):
        return super().cardinality(a)
