# pylint: disable=missing-class-docstring,no-self-use
from __future__ import annotations

import gc
import pickle
import unittest

import claripy


class TestPickle(unittest.TestCase):
    def test_pickle_ast(self):
        bz = claripy.backends.z3

        a = claripy.BVV(1, 32)
        b = claripy.BVS("x", 32, explicit_name=True)

        c = a + b
        assert bz.convert(c).__module__ == "z3.z3"
        assert str(bz.convert(c)), "1 + x"

        c_copy = pickle.loads(pickle.dumps(c, -1))
        assert c_copy is c
        assert bz.convert(c_copy).__module__ == "z3.z3"
        assert str(bz.convert(c_copy)) == "1 + x"

    def test_pickle_frontend(self):
        s = claripy.Solver()
        x = claripy.BVS("x", 32)

        s.add(x == 1)
        assert s.eval(x, 10), (1,)

        ss = pickle.dumps(s)
        del s

        gc.collect()

        s = pickle.loads(ss)
        assert s.eval(x, 10), (1,)

    def test_identity(self):
        a = claripy.BVV(1, 32)
        b = claripy.BVS("x", 32)
        c = a + b
        d = a + b * 50

        c_info = pickle.dumps(c)
        d_info = pickle.dumps(d)

        cc = pickle.loads(c_info)
        assert str(cc) == str(c)
        cd = pickle.loads(d_info)
        assert str(cd) == str(d)
        assert c.args[0] is d.args[0]

        s = claripy.Solver()
        x = claripy.BVS("x", 32)
        s.add(x == 3)
        s.finalize()
        ss = pickle.loads(pickle.dumps(s))
        assert str(s.constraints) == str(ss.constraints)
        assert str(s.variables) == str(ss.variables)

        s = claripy.SolverComposite()
        x = claripy.BVS("x", 32)
        s.add(x == 3)
        s.finalize()
        ss = pickle.loads(pickle.dumps(s))
        old_constraint_sets = [[hash(j) for j in k.constraints] for k in s._solver_list]
        new_constraint_sets = [[hash(j) for j in k.constraints] for k in ss._solver_list]
        assert old_constraint_sets == new_constraint_sets
        assert str(s.variables) == str(ss.variables)


if __name__ == "__main__":
    unittest.main()
