import claripy
import nose

def test_simple_merging():
    yield raw_simple_merging, claripy.Solver
    yield raw_simple_merging, claripy.SolverHybrid
    yield raw_simple_merging, claripy.SolverComposite

def raw_simple_merging(solver_type):
    s1 = solver_type()
    s2 = solver_type()
    w = claripy.BVS("w", 8)
    x = claripy.BVS("x", 8)
    y = claripy.BVS("y", 8)
    z = claripy.BVS("z", 8)
    m = claripy.BVS("m", 8)

    s1.add([x == 1, y == 10])
    s2.add([x == 2, z == 20, w == 5])
    _, sm = s1.merge([s2], [ m == 0, m == 1 ])

    nose.tools.assert_equal(s1.eval(x, 1), (1,))
    nose.tools.assert_equal(s2.eval(x, 1), (2,))

    sm1 = sm.branch()
    sm1.add(x == 1)
    nose.tools.assert_equal(sm1.eval(x, 1), (1,))
    nose.tools.assert_equal(sm1.eval(y, 1), (10,))
    nose.tools.assert_equal(sm1.eval(z, 1), (0,))
    nose.tools.assert_equal(sm1.eval(w, 1), (0,))

    sm2 = sm.branch()
    sm2.add(x == 2)
    nose.tools.assert_equal(sm2.eval(x, 1), (2,))
    nose.tools.assert_equal(sm2.eval(y, 1), (0,))
    nose.tools.assert_equal(sm2.eval(z, 1), (20,))
    nose.tools.assert_equal(sm2.eval(w, 1), (5,))

    sm1 = sm.branch()
    sm1.add(m == 0)
    nose.tools.assert_equal(sm1.eval(x, 1), (1,))
    nose.tools.assert_equal(sm1.eval(y, 1), (10,))
    nose.tools.assert_equal(sm1.eval(z, 1), (0,))
    nose.tools.assert_equal(sm1.eval(w, 1), (0,))

    sm2 = sm.branch()
    sm2.add(m == 1)
    nose.tools.assert_equal(sm2.eval(x, 1), (2,))
    nose.tools.assert_equal(sm2.eval(y, 1), (0,))
    nose.tools.assert_equal(sm2.eval(z, 1), (20,))
    nose.tools.assert_equal(sm2.eval(w, 1), (5,))

    m2 = claripy.BVS("m2", 32)
    _, smm = sm1.merge([sm2], [ m2 == 0, m2 == 1 ])

    smm_1 = smm.branch()
    smm_1.add(x == 1)
    nose.tools.assert_equal(smm_1.eval(x, 1), (1,))
    nose.tools.assert_equal(smm_1.eval(y, 1), (10,))
    nose.tools.assert_equal(smm_1.eval(z, 1), (0,))
    nose.tools.assert_equal(smm_1.eval(w, 1), (0,))

    smm_2 = smm.branch()
    smm_2.add(m == 1)
    nose.tools.assert_equal(smm_2.eval(x, 1), (2,))
    nose.tools.assert_equal(smm_2.eval(y, 1), (0,))
    nose.tools.assert_equal(smm_2.eval(z, 1), (20,))
    nose.tools.assert_equal(smm_2.eval(w, 1), (5,))

    so = solver_type()
    so.add(w == 0)

    sa = so.branch()
    sb = so.branch()
    sa.add(x == 1)
    sb.add(x == 2)
    _, sm = sa.merge([sb], [ m == 0, m == 1 ])

    smc = sm.branch()
    smd = sm.branch()
    smc.add(y == 3)
    smd.add(y == 4)

    _, smm = smc.merge([smd], [ m2 == 0, m2 == 1 ])
    wxy = claripy.Concat(w, x, y)

    smm_1 = smm.branch()
    smm_1.add(wxy == 0x000103)
    nose.tools.assert_true(smm_1.satisfiable())

    smm_1 = smm.branch()
    smm_1.add(wxy == 0x000104)
    nose.tools.assert_true(smm_1.satisfiable())

    smm_1 = smm.branch()
    smm_1.add(wxy == 0x000203)
    nose.tools.assert_true(smm_1.satisfiable())

    smm_1 = smm.branch()
    smm_1.add(wxy == 0x000204)
    nose.tools.assert_true(smm_1.satisfiable())

    smm_1 = smm.branch()
    smm_1.add(wxy != 0x000103)
    smm_1.add(wxy != 0x000104)
    smm_1.add(wxy != 0x000203)
    smm_1.add(wxy != 0x000204)
    nose.tools.assert_false(smm_1.satisfiable())

if __name__ == '__main__':
    for func, param in test_simple_merging():
        func(param)
