# pylint: disable=missing-class-docstring,no-self-use
from __future__ import annotations

from unittest import TestCase

import claripy
from claripy import BVS, BoolS, Not, Xor, false, ite_dict, true


class TestBool(TestCase):
    def test_xor_simplification(self):
        a = BoolS("a")
        b = BoolS("b")

        # Xor with a concrete operand simplifies away
        assert Xor(a, false()) is a
        assert Xor(false(), a) is a
        assert Xor(a, true()) is Not(a)
        assert Xor(true(), a) is Not(a)

        # the operator overload constructs a Xor op
        assert (a ^ b).op == "Xor"

    def test_xor_concrete(self):
        for x in (True, False):
            for y in (True, False):
                expr = Xor(true() if x else false(), true() if y else false())
                assert claripy.backends.concrete.eval(expr, 1)[0] == (x ^ y)

    def test_xor_solve(self):
        a = BoolS("a")
        b = BoolS("b")
        s = claripy.Solver()
        s.add(Xor(a, b))
        s.add(a)
        assert s.eval(b, 2) == (False,)

    def test_ite_dict_is_balanced(self):
        case_even = ite_dict(
            BVS("A", 8),
            {
                1: 11,
                2: 22,
                3: 33,
                4: 44,
            },
            BVS("B", 8),
        )

        assert case_even.args[1].depth == case_even.args[2].depth

        case_odd = ite_dict(
            BVS("A", 8),
            {
                1: 11,
                2: 22,
                3: 33,
                4: 44,
                5: 55,
            },
            BVS("B", 8),
        )

        assert case_odd.args[1].depth == case_odd.args[2].depth + 1
