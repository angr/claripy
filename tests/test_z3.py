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
        z = claripy.backend_manager.backends.z3

        s = z.solver()
        x = claripy.BVS("x", 8)

        rng = (
            0,
            2**x.length - 1,
        )
        assert z.satisfiable(solver=s)
        assert z.min(x, solver=s) == rng[0]
        assert z.max(x, solver=s) == rng[1]

        for i in range(rng[0], rng[1] + 1):
            # ==
            assert z.min(x, solver=s, extra_constraints=(x == i,)) == i
            assert z.max(x, solver=s, extra_constraints=(x == i,)) == i
            # <=
            assert z.min(x, solver=s, extra_constraints=(x <= i,)) == rng[0]
            assert z.max(x, solver=s, extra_constraints=(x <= i,)) == i
            # >=
            assert z.min(x, solver=s, extra_constraints=(x >= i,)) == i
            assert z.max(x, solver=s, extra_constraints=(x >= i,)) == rng[1]


if __name__ == "__main__":
    unittest.main()
