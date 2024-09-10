# pylint: disable=missing-class-docstring,no-self-use
from __future__ import annotations

import unittest

import claripy


class TestAST(unittest.TestCase):
    def test_lite_repr(self):
        one = claripy.BVV(1, 8)
        two = claripy.BVV(2, 8)
        a = claripy.BVS("a", 8, explicit_name=True)
        b = claripy.BVS("b", 8, explicit_name=True)

        assert (a + one * b + two).shallow_repr() == "<BV8 a + 1 * b + 2>"
        assert ((a + one) * (b + two)).shallow_repr() == "<BV8 (a + 1) * (b + 2)>"
        assert (a * one + b * two).shallow_repr() == "<BV8 a * 1 + b * 2>"
        assert (
            (one + a) * (two + b) + (two + a) * (one + b)
        ).shallow_repr() == "<BV8 (1 + a) * (2 + b) + (2 + a) * (1 + b)>"

    def test_associativity(self):
        x = claripy.BVS("x", 8, explicit_name=True)
        y = claripy.BVS("y", 8, explicit_name=True)
        z = claripy.BVS("z", 8, explicit_name=True)
        w = claripy.BVS("w", 8, explicit_name=True)

        assert (x - (y - (z - w))).shallow_repr() == "<BV8 x - (y - (z - w))>"
        assert (x - y - z - w).shallow_repr() == "<BV8 x - y - z - w>"
        assert (x * (y * (z * w))).shallow_repr() == (x * y * z * w).shallow_repr()
        assert (x * y * z * w).shallow_repr() == "<BV8 x * y * z * w>"
        assert (x + y - z - w).shallow_repr() == "<BV8 x + y - z - w>"
        assert (x + (y - (z - w))).shallow_repr() == "<BV8 x + (y - (z - w))>"
        assert (x * y // z % w).shallow_repr() == "<BV8 x * y / z % w>"
        assert (x * (y // (z % w))).shallow_repr() == "<BV8 x * (y / (z % w))>"

    def test_is_leaf(self):
        x = claripy.BVS("x", 8, explicit_name=True)
        y = claripy.BVS("y", 8, explicit_name=True)

        assert x.is_leaf()
        assert y.is_leaf()
        assert (x + y).is_leaf() is False
        assert (x * y).is_leaf() is False
        assert (x - y).is_leaf() is False
        assert (x // y).is_leaf() is False
        assert (x % y).is_leaf() is False
        assert (x**y).is_leaf() is False
        assert (x & y).is_leaf() is False
        assert (x | y).is_leaf() is False
        assert (x ^ y).is_leaf() is False
        assert (x << y).is_leaf() is False
        assert (x >> y).is_leaf() is False
        assert (x == y).is_leaf() is False


if __name__ == "__main__":
    unittest.main()
