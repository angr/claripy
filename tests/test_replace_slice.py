from __future__ import annotations

from unittest import TestCase, main

import claripy


def is_true_under_cst(solver: claripy.Solver, check: claripy.ast.Bool):
    return not solver.satisfiable(extra_constraints=[claripy.Not(check)])


class TestReplaceSlice(TestCase):

    def test_replace_slice(self):
        x = claripy.BVS("X", 64)
        y = claripy.BVS("Y", 64)
        z = claripy.BVS("Z", 64)

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
        new = y[44:6]
        # expected expression after slice: x[63:51] .. y[44:6] .. x[11:0]
        assert claripy.simplify(claripy.replace_slice(expr, old, new)) is claripy.Concat(x[:51], y[44:6], x[11:])

        expr = claripy.Concat(x[30:15], y[10:4], x[17:10])
        old = x[18:16]
        new = z[2:]
        # expected expression after slice: x[30:19] .. z[2:0] .. x[15:15] .. y[10:4] .. z[1:0] .. x[15:10]
        assert claripy.simplify(claripy.replace_slice(expr, old, new)) is claripy.Concat(
            x[30:19], z[2:], x[15:15], y[10:4], z[1:], x[15:10]
        )


if __name__ == "__main__":
    main()
