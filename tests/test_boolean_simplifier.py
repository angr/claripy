from __future__ import annotations

import unittest

import claripy
from claripy.boolean_simplifier import linearize_parent_first, simplify_boolean_expr

true = claripy.true
false = claripy.false
x = claripy.BoolS("x", explicit_name=True)
y = claripy.BoolS("y", explicit_name=True)
z = claripy.BoolS("z", explicit_name=True)
foreign = claripy.BVV(0, 8)


class TestLinearizeParentFirst(unittest.TestCase):
    def test_leaf(self):
        for case in [true, false, x, foreign]:
            with self.subTest(leaf=case):
                linearized = linearize_parent_first(case)
                self.assertTrue(len(linearized) == 1 and linearized[0].identical(case))

    def test_not_leaf(self):
        for case in [
            (~x, [~x, x]),
            (~x & y, [~x & y, ~x, x, y]),
        ]:
            with self.subTest(leaf=case):
                linearized = linearize_parent_first(case[0])
                for l, r in zip(linearized, case[1], strict=True):
                    self.assertTrue(l.identical(r))

    def test_complex(self):
        for case in [
            (
                (x | y) & (x | z),
                [
                    (x | y) & (x | z),
                    x | y,
                    x,
                    y,
                    x | z,
                    x,
                    z,
                ],
            ),
        ]:
            with self.subTest(leaf=case):
                linearized = linearize_parent_first(case[0])
                for l, r in zip(linearized, case[1], strict=True):
                    self.assertTrue(l.identical(r))


class TestBooleanSimplifier(unittest.TestCase):
    def test_leaves(self):
        for case in [true, false, x, foreign]:
            with self.subTest(leaf=case):
                self.assertTrue(simplify_boolean_expr(case).identical(case))

    def test_not(self):
        for case in [
            # Constant elimination
            (~true, false),
            (~false, true),
            # Double negation elimination
            (~x, ~x),
            (~~true, true),
        ]:
            with self.subTest(case=case):
                self.assertTrue(simplify_boolean_expr(case[0]).identical(case[1]))

    def test_and(self):
        for case in [
            # Constant elimination
            (true & true, true),
            (true & false, false),
            (false & true, false),
            (false & false, false),
            (x & true, x),
            (x & false, false),
            (true & x, x),
            (false & x, false),
            # Indempotent elimination
            (x & x, x),
            # Xor elimination
            (~x & x, false),
            (x & ~x, false),
            # Absorption
            (x | y, x | y),
            (x | z, x | z),
            ((x | y) & (x | z), x | (y & z)),
        ]:
            with self.subTest(case=case):
                self.assertTrue(simplify_boolean_expr(case[0]).identical(case[1]))

    def test_or(self):
        for case in [
            # Constant elimination
            (true | true, true),
            (true | false, true),
            (false | true, true),
            (false | false, false),
            (x | true, true),
            (x | false, x),
            (true | x, true),
            (false | x, x),
            # Indempotent elimination
            (x | x, x),
            # Xor elimination
            (~x | x, true),
            (x | ~x, true),
            # Absorption
            (x & y, x & y),
            (x & z, x & z),
            ((x & y) | (x & z), x & (y | z)),
        ]:
            with self.subTest(case=case):
                self.assertTrue(simplify_boolean_expr(case[0]).identical(case[1]))
