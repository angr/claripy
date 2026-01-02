from __future__ import annotations

from unittest import TestCase, main

import claripy


def is_true_under_cst(solver: claripy.Solver, check: claripy.ast.Bool):
    return not solver.satisfiable(extra_constraints=[claripy.Not(check)])


class TestReplaceSlice(TestCase):

    def test_replace_slice(self):
        x = claripy.BVS("X", 64)
        y = claripy.BVS("Y", 64)

        solver = claripy.Solver()
        expr = x
        old = x[2:1]
        new = y[7:6]
        solver.add(old == new)
        replaced = claripy.replace_slice(expr, x[2:1], y[7:6])
        assert is_true_under_cst(solver, expr == replaced)
        assert replaced is not x  # X != X proof

        expr = x
        old = x[50:12]
        new = y
        # expected expression after slice: x[63:51] .. y .. x[11:0]
        assert claripy.replace_slice(expr, old, new) is claripy.Concat(x[:51], y, x[11:])


if __name__ == "__main__":
    main()
