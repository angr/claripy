# pylint: disable=missing-class-docstring,no-self-use
from __future__ import annotations

from unittest import TestCase

from claripy import BVS, ite_dict


class TestBool(TestCase):
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
