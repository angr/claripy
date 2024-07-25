# pylint: disable=missing-class-docstring,no-self-use
from __future__ import annotations

import unittest

import claripy


class TestRegressions(unittest.TestCase):
    def test_issue16(self):
        s = claripy.SolverComposite()

        c = claripy.BVS("test", 32)
        s.add(c[7:0] != 0)

        assert s.satisfiable()
        s.add(c == 0)

        assert not s.satisfiable(extra_constraints=[claripy.BVS("lol", 32) == 0])
        assert not s.satisfiable()


if __name__ == "__main__":
    unittest.main()
