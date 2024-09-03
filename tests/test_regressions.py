# pylint: disable=missing-class-docstring,no-self-use
from __future__ import annotations

import unittest

import claripy


class TestRegressions(unittest.TestCase):
    def test_issue_16(self):
        s = claripy.SolverComposite()

        c = claripy.BVS("test", 32)
        s.add(c[7:0] != 0)

        assert s.satisfiable()
        s.add(c == 0)

        assert not s.satisfiable(extra_constraints=[claripy.BVS("lol", 32) == 0])
        assert not s.satisfiable()

    def test_issue_324(self):
        s = claripy.Solver()
        x = claripy.BVS("x", 64)
        y = claripy.BVS("y", 64)
        s.add(x - y >= 4)
        s.add(y > 0)
        assert s.min(x) == 0
        assert s.min(x, extra_constraints=[x > 0]) == 1

    def test_issue_324_2(self):
        ast = claripy.BVS("a", 64) + 0xFF

        s1 = claripy.Solver()

        min_1 = s1.min(ast)
        max_1 = s1.max(ast)
        min_2 = s1.min(ast)
        max_2 = s1.max(ast)

        assert min_1 == min_2
        assert max_1 == max_2

        s2 = claripy.Solver()

        min_3 = s2.min(ast)
        max_3 = s2.max(ast)
        min_4 = s2.min(ast)
        max_4 = s2.max(ast)

        assert min_1 == min_2 == min_3 == min_4
        assert max_1 == max_2 == max_3 == max_4


if __name__ == "__main__":
    unittest.main()
