# pylint: disable=missing-class-docstring,no-self-use
from __future__ import annotations

import unittest

import claripy


class TestMerging(unittest.TestCase):
    def test_simple_merging_solver(self):
        self.raw_simple_merging(claripy.Solver)

    def test_simple_merging_solverhybrid(self):
        self.raw_simple_merging(claripy.SolverHybrid)

    def test_simple_merging_solvercomposite(self):
        self.raw_simple_merging(claripy.SolverComposite)

    def raw_simple_merging(self, solver_type):
        s1 = solver_type()
        s2 = solver_type()
        w = claripy.BVS("w", 8)
        x = claripy.BVS("x", 8)
        y = claripy.BVS("y", 8)
        z = claripy.BVS("z", 8)
        m = claripy.BVS("m", 8)

        s1.add([x == 1, y == 10])
        s2.add([x == 2, z == 20, w == 5])
        _, sm = s1.merge([s2], [m == 0, m == 1])

        self.assertEqual(s1.eval(x, 1), (1,))
        self.assertEqual(s2.eval(x, 1), (2,))

        sm1 = sm.branch()
        sm1.add(x == 1)
        self.assertEqual(sm1.eval(x, 1), (1,))
        self.assertEqual(sm1.eval(y, 1), (10,))
        self.assertEqual(sm1.eval(z, 1), (0,))
        self.assertEqual(sm1.eval(w, 1), (0,))

        sm2 = sm.branch()
        sm2.add(x == 2)
        self.assertEqual(sm2.eval(x, 1), (2,))
        self.assertEqual(sm2.eval(y, 1), (0,))
        self.assertEqual(sm2.eval(z, 1), (20,))
        self.assertEqual(sm2.eval(w, 1), (5,))

        sm1 = sm.branch()
        sm1.add(m == 0)
        self.assertEqual(sm1.eval(x, 1), (1,))
        self.assertEqual(sm1.eval(y, 1), (10,))
        self.assertEqual(sm1.eval(z, 1), (0,))
        self.assertEqual(sm1.eval(w, 1), (0,))

        sm2 = sm.branch()
        sm2.add(m == 1)
        self.assertEqual(sm2.eval(x, 1), (2,))
        self.assertEqual(sm2.eval(y, 1), (0,))
        self.assertEqual(sm2.eval(z, 1), (20,))
        self.assertEqual(sm2.eval(w, 1), (5,))

        m2 = claripy.BVS("m2", 32)
        _, smm = sm1.merge([sm2], [m2 == 0, m2 == 1])

        smm_1 = smm.branch()
        smm_1.add(x == 1)
        self.assertEqual(smm_1.eval(x, 1), (1,))
        self.assertEqual(smm_1.eval(y, 1), (10,))
        self.assertEqual(smm_1.eval(z, 1), (0,))
        self.assertEqual(smm_1.eval(w, 1), (0,))

        smm_2 = smm.branch()
        smm_2.add(m == 1)
        self.assertEqual(smm_2.eval(x, 1), (2,))
        self.assertEqual(smm_2.eval(y, 1), (0,))
        self.assertEqual(smm_2.eval(z, 1), (20,))
        self.assertEqual(smm_2.eval(w, 1), (5,))

        so = solver_type()
        so.add(w == 0)

        sa = so.branch()
        sb = so.branch()
        sa.add(x == 1)
        sb.add(x == 2)
        _, sm = sa.merge([sb], [m == 0, m == 1])

        smc = sm.branch()
        smd = sm.branch()
        smc.add(y == 3)
        smd.add(y == 4)

        _, smm = smc.merge([smd], [m2 == 0, m2 == 1])
        wxy = claripy.Concat(w, x, y)

        smm_1 = smm.branch()
        smm_1.add(wxy == 0x000103)
        self.assertTrue(smm_1.satisfiable())

        smm_1 = smm.branch()
        smm_1.add(wxy == 0x000104)
        self.assertTrue(smm_1.satisfiable())

        smm_1 = smm.branch()
        smm_1.add(wxy == 0x000203)
        self.assertTrue(smm_1.satisfiable())

        smm_1 = smm.branch()
        smm_1.add(wxy == 0x000204)
        self.assertTrue(smm_1.satisfiable())

        smm_1 = smm.branch()
        smm_1.add(wxy != 0x000103)
        smm_1.add(wxy != 0x000104)
        smm_1.add(wxy != 0x000203)
        smm_1.add(wxy != 0x000204)
        self.assertFalse(smm_1.satisfiable())

        s3 = solver_type()
        s3.add(w == 0)
        s4 = solver_type()
        _, sm = s3.merge([s4], [m == 0, m == 1])
        self.assertEqual(len(sm.eval(w, 2)), 2)


if __name__ == "__main__":
    unittest.main()
