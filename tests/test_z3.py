# pylint: disable=missing-class-docstring,no-self-use
from __future__ import annotations

import unittest

import claripy


class TestZ3(unittest.TestCase):
    """
    A class used for testing z3
    """

    def test_extrema(self):
        """
        Test the _extrema function within the z3 backend
        """
        z = claripy.backends.z3

        s = z.solver()
        x = claripy.BVS("x", 8)
        range_ = (0, 2**x.length - 1)

        assert z.min(x, solver=s) == range_[0]
        assert z.max(x, solver=s) == range_[1]

        for i in range(0, range_[1] + 1, 10):
            # ==
            assert z.min(x, solver=s, extra_constraints=(x == i,)) == i
            assert z.max(x, solver=s, extra_constraints=(x == i,)) == i
            # <=
            assert z.min(x, solver=s, extra_constraints=(x <= i,)) == range_[0]
            assert z.max(x, solver=s, extra_constraints=(x <= i,)) == i
            # >=
            assert z.min(x, solver=s, extra_constraints=(x >= i,)) == i
            assert z.max(x, solver=s, extra_constraints=(x >= i,)) == range_[1]


if __name__ == "__main__":
    unittest.main()
