import claripy
import nose

import logging
l = logging.getLogger('claripy.test.solver')

solver_list = (claripy.Solver, claripy.SolverReplacement, claripy.SolverHybrid, claripy.SolverComposite, claripy.SolverCacheless)

def test_solver():
    for s in solver_list:
        yield raw_solver, s

def test_hybrid_solver():
    s = claripy.SolverHybrid()

    x = claripy.BVS('x', 32, min=0, max=10, stride=2)
    y = claripy.BVS('y', 32, min=20, max=30, stride=5)

    # TODO: for now, the stride isn't respected in symbolic mode, but we'll fix that next.
    # until we do, let's add constraints
    s.add(x <= 10)
    s.add(x % 2 == 0)
    s.add(y >= 20)
    s.add(y <= 30)
    s.add((y-20) % 5 == 0)
    s.add(x != 8)

    nose.tools.assert_items_equal(s.eval(x, 20, exact=False), (0, 2, 4, 6, 8, 10))
    nose.tools.assert_items_equal(s.eval(x, 20), (0, 2, 4, 6, 10))
    nose.tools.assert_items_equal(s.eval(y, 20, exact=False), (20, 25, 30))
    nose.tools.assert_items_equal(s.eval(y, 20), (20, 25, 30))

    # now constrain things further so that the VSA overapproximates
    s.add(x <= 4)
    nose.tools.assert_items_equal(s.eval(x, 20, exact=False), (0, 2, 4))
    nose.tools.assert_items_equal(s.eval(x, 20), (0, 2, 4))

    s.add(y >= 27)
    nose.tools.assert_items_equal(s.eval(y, 20, exact=False), (30,))
    nose.tools.assert_items_equal(s.eval(y, 20), (30,))

    t = claripy.SolverHybrid()
    x = claripy.BVS('x', 32)
    t.add(x <= 10)
    print t.eval(x, 80, exact=False)
    nose.tools.assert_equal(len(t.eval(x, 5, exact=False)), 5)
    nose.tools.assert_equal(len(t.eval(x, 5, exact=False)), 5)
    nose.tools.assert_equal(len(t.eval(x, 6, exact=False)), 6)
    nose.tools.assert_equal(len(t.eval(x, 8, exact=False)), 8)
    nose.tools.assert_equal(len(t.eval(x, 99, exact=False)), 11)

def test_replacement_solver():
    sr = claripy.SolverReplacement()
    x = claripy.BVS('x', 32)
    nose.tools.assert_equals(len(sr.eval(x, 10)), 10)
    sr.add_replacement(x, claripy.BVV(0x101, 32))
    nose.tools.assert_items_equal(sr.eval(x, 10), [0x101])

    y = claripy.BVS('y', 32)
    sr.add([y+1 == 200])
    assert (y+1).cache_key in sr._replacements
    assert sr._replacement(y+1) is claripy.BVV(200, 32)

    srb = sr.branch()
    assert len(srb.constraints) == len(sr.constraints) #pylint:disable=no-member
    assert (y+1).cache_key in sr._replacements
    assert sr._replacement(y+1) is claripy.BVV(200, 32)

    sr = claripy.SolverReplacement()
    b = claripy.BoolS('b')
    assert sr._replacement(b) is b
    sr.add(claripy.Not(b))
    assert sr._replacement(b) is claripy.false

    sr = claripy.SolverReplacement(claripy.SolverVSA(), complex_auto_replace=True)
    x = claripy.BVS('x', 64)
    sr.add([x + 8 <= 0xffffffffffffffff])
    sr.add([x + 8 >= 0])
    assert sr._replacement(x) is not x

def raw_solver(solver_type):
    #bc = claripy.backends.BackendConcrete(clrp)
    #bz = claripy.backends.BackendZ3(clrp)
    #claripy.expression_backends = [ bc, bz, ba ]

    print "YOYO"
    s = solver_type()

    s.simplify()

    x = claripy.BVS('x', 32)
    y = claripy.BVS('y', 32)
    z = claripy.BVS('z', 32)

    l.debug("adding constraints")

    s.add(x == 10)
    s.add(y == 15)

    # Batch evaluation
    results = s.batch_eval([x + 5, x + 6, 3], 2)
    nose.tools.assert_equal(len(results), 1)
    nose.tools.assert_equal(results[0][0], 15) # x + 5
    nose.tools.assert_equal(results[0][1], 16) # x + 6
    nose.tools.assert_equal(results[0][2], 3)  # constant

    l.debug("checking")
    nose.tools.assert_true(s.satisfiable())
    nose.tools.assert_false(s.satisfiable(extra_constraints=[x == 5]))
    nose.tools.assert_equal(s.eval(x + 5, 1)[0], 15)
    nose.tools.assert_true(s.solution(x + 5, 15))
    nose.tools.assert_true(s.solution(x, 10))
    nose.tools.assert_true(s.solution(y, 15))
    nose.tools.assert_false(s.solution(y, 13))

    shards = s.split()
    nose.tools.assert_equal(len(shards), 2)
    nose.tools.assert_equal(len(shards[0].variables), 1)
    nose.tools.assert_equal(len(shards[1].variables), 1)
    if isinstance(s, claripy.frontend_mixins.ConstraintExpansionMixin) or (
        isinstance(s, claripy.frontends.HybridFrontend) and
        isinstance(s._exact_frontend, claripy.frontend_mixins.ConstraintExpansionMixin)
    ): #the hybrid frontend actually uses the exact frontend for the split
        nose.tools.assert_equal({ len(shards[0].constraints), len(shards[1].constraints) }, { 2, 1 }) # adds the != from the solution() check
    if isinstance(s, claripy.frontends.ReplacementFrontend):
        nose.tools.assert_equal({ len(shards[0].constraints), len(shards[1].constraints) }, { 1, 1 }) # not a caching frontend

    # test result caching
    s = solver_type()
    s.add(x == 10)
    s.add(y == 15)
    nose.tools.assert_false(s.satisfiable(extra_constraints=(x==5,)))
    nose.tools.assert_true(s.satisfiable())

    s = solver_type()
    #claripy.expression_backends = [ bc, ba, bz ]
    s.add(claripy.UGT(x, 10))
    s.add(claripy.UGT(x, 20))
    s.simplify()
    nose.tools.assert_equal(len(s.constraints), 1)
    #nose.tools.assert_equal(str(s.constraints[0]._obj), "Not(ULE(x <= 20))")

    s.add(claripy.UGT(y, x))
    s.add(claripy.ULT(z, 5))

    # test that duplicate constraints are ignored
    old_count = len(s.constraints)
    s.add(claripy.ULT(z, 5))
    nose.tools.assert_equal(len(s.constraints), old_count)

    #print "========================================================================================"
    #print "========================================================================================"
    #print "========================================================================================"
    #print "========================================================================================"
    #a = s.eval(z, 100)
    #print "ANY:", a
    #print "========================================================================================"
    #mx = s.max(z)
    #print "MAX",mx
    #print "========================================================================================"
    #mn = s.min(z)
    #print "MIN",mn
    #print "========================================================================================"
    #print "========================================================================================"
    #print "========================================================================================"
    #print "========================================================================================"

    print "CONSTRATINT COUNTS:", [ len(_.constraints) for _ in s.split() ]

    nose.tools.assert_equal(s.max(z), 4)
    nose.tools.assert_equal(s.min(z), 0)
    nose.tools.assert_equal(s.min(y), 22)
    nose.tools.assert_equal(s.max(y), 2**y.size()-1)

    print "CONSTRATINT COUNTS:", [ len(_.constraints) for _ in s.split() ]

    ss = s.split()
    nose.tools.assert_equal(len(ss), 2)
    #if isinstance(s, claripy.frontend_mixins.ConstraintExpansionMixin):
    #   nose.tools.assert_equal({ len(_.constraints) for _ in ss }, { 3, 2 }) # constraints from min or max

    # Batch evaluation
    s.add(y < 24)
    s.add(z < x) # Just to make sure x, y, and z belong to the same solver, since batch evaluation does not support the
                 # situation where expressions belong to more than one solver
    results = s.batch_eval([x, y, z], 20)
    nose.tools.assert_set_equal(
        set(results),
        {(21L, 23L, 1L), (22L, 23L, 3L), (22L, 23L, 2L), (22L, 23L, 4L), (21L, 22L, 4L), (21L, 23L, 4L), (22L, 23L, 0L),
         (22L, 23L, 1L), (21L, 22L, 1L), (21L, 22L, 3L), (21L, 22L, 2L), (21L, 22L, 0L), (21L, 23L, 0L), (21L, 23L, 2L),
         (21L, 23L, 3L)
        }
    )

    # test that False makes it unsat
    s = solver_type()
    s.add(claripy.BVV(1,1) == claripy.BVV(1,1))
    nose.tools.assert_true(s.satisfiable())
    s.add(claripy.BVV(1,1) == claripy.BVV(0,1))
    nose.tools.assert_false(s.satisfiable())

    # test extra constraints
    s = solver_type()
    x = claripy.BVS('x', 32)
    nose.tools.assert_items_equal(s.eval(x, 2, extra_constraints=[x==10]), ( 10, ))
    s.add(x == 10)
    nose.tools.assert_false(s.solution(x, 2))
    nose.tools.assert_true(s.solution(x, 10))

    # test result caching

    if isinstance(s, claripy.frontend_mixins.ModelCacheMixin):
        count = claripy._backends_module.backend_z3.solve_count

        s = solver_type()
        x = claripy.BVS('x', 32)
        s.add(x == 10)
        nose.tools.assert_true(s.satisfiable())
        assert claripy._backends_module.backend_z3.solve_count == count + 1
        nose.tools.assert_equals(s.eval(x, 1)[0], 10)
        assert claripy._backends_module.backend_z3.solve_count == count + 1
        s.add(x == 10)
        s.add(x > 9)
        nose.tools.assert_equals(s.eval(x, 1)[0], 10)
        assert claripy._backends_module.backend_z3.solve_count == count + 1

        y = claripy.BVS('y', 32)
        s.add(y < 999)
        assert s.satisfiable()
        assert claripy._backends_module.backend_z3.solve_count == count + 1
        nose.tools.assert_equals(s.eval(y, 1)[0], 0)
        assert claripy._backends_module.backend_z3.solve_count == count + 1

def test_solver_branching():
    for s in solver_list:
        yield raw_solver_branching, s

def raw_solver_branching(solver_type):
    s = solver_type()
    x = claripy.BVS("x", 32)
    y = claripy.BVS("y", 32)
    s.add(claripy.UGT(x, y))
    s.add(claripy.ULT(x, 10))

    nose.tools.assert_greater(s.eval(x, 1)[0], 0)

    t = s.branch()
    if isinstance(s, claripy.frontends.FullFrontend):
        nose.tools.assert_is(s._tls.solver, t._tls.solver)
        nose.tools.assert_true(s._finalized)
        nose.tools.assert_true(t._finalized)
    t.add(x == 5)
    #if isinstance(s, claripy.FullFrontend):
    #   nose.tools.assert_is(t._solver, None)

    s.add(x == 3)
    nose.tools.assert_true(s.satisfiable())
    t.add(x == 3)
    nose.tools.assert_false(t.satisfiable())

    s.add(y == 2)
    nose.tools.assert_true(s.satisfiable())
    nose.tools.assert_equals(s.eval(x, 1)[0], 3)
    nose.tools.assert_equals(s.eval(y, 1)[0], 2)
    nose.tools.assert_false(t.satisfiable())

def test_combine():
    for s in solver_list:
        yield raw_combine, s

def raw_combine(solver_type):
    s10 = solver_type()
    s20 = solver_type()
    s30 = solver_type()
    x = claripy.BVS("x", 32)

    s10.add(x >= 10)
    s20.add(x <= 20)
    s30.add(x == 30)

    nose.tools.assert_true(s10.satisfiable())
    nose.tools.assert_true(s20.satisfiable())
    nose.tools.assert_true(s30.satisfiable())
    nose.tools.assert_true(s10.combine([s20]).satisfiable())
    nose.tools.assert_true(s20.combine([s10]).satisfiable())
    nose.tools.assert_true(s30.combine([s10]).satisfiable())
    nose.tools.assert_false(s30.combine([s20]).satisfiable())
    nose.tools.assert_items_equal(s30.combine([s10]).eval(x, 1), ( 30, ))
    nose.tools.assert_equal(len(s30.combine([s10]).constraints), 2)

def test_composite_solver():
    #pylint:disable=no-member
    s = claripy.SolverComposite()
    x = claripy.BVS("x", 32)
    y = claripy.BVS("y", 32)
    z = claripy.BVS("z", 32)
    c = claripy.And(x == 1, y == 2, z == 3)
    s.add(c)
    nose.tools.assert_equals(len(s._solver_list), 3)
    nose.tools.assert_true(s.satisfiable())

    s.add(x < y)
    nose.tools.assert_equal(len(s._solver_list), 2)
    nose.tools.assert_true(s.satisfiable())

    s.simplify()
    nose.tools.assert_equal(len(s._solver_list), 3)
    nose.tools.assert_true(s.satisfiable())

    s1 = s.branch()
    nose.tools.assert_equal(len(s1._solver_list), 3)

    s1.add(x > y)
    nose.tools.assert_equal(len(s1._solver_list), 2)
    nose.tools.assert_false(s1.satisfiable())
    nose.tools.assert_equal(len(s._solver_list), 3)
    nose.tools.assert_true(s.satisfiable())

    s.add(claripy.BVV(1, 32) == claripy.BVV(2, 32))
    nose.tools.assert_equal(len(s._solver_list), 3)
    nose.tools.assert_false(s.satisfiable())

    ss = s.branch()
    nose.tools.assert_equal(len(ss._solver_list), 3)
    nose.tools.assert_false(ss.satisfiable())

    s = claripy.SolverComposite()
    x = claripy.BVS("x", 32)
    y = claripy.BVS("y", 32)
    z = claripy.BVS("z", 32)
    c = claripy.And(x == 1, y == 2, z == 3)
    s.add(c)

    if isinstance(s._template_frontend, claripy.frontend_mixins.ModelCacheMixin):
        assert len(s._solver_list) == 3
        count = claripy._backends_module.backend_z3.solve_count
        assert s.satisfiable()
        assert claripy._backends_module.backend_z3.solve_count == count + 3
        assert list(s.eval(x+y, 1)) == [3]
        assert claripy._backends_module.backend_z3.solve_count == count + 3

def test_minmax():
    s = claripy.Solver()
    x = claripy.BVS("x", 32)

    nose.tools.assert_equal(s.max(x), 2**32-1)
    nose.tools.assert_equal(s.min(x), 0)
    nose.tools.assert_true(s.satisfiable())

def test_composite_discrepancy():
    a = claripy.BVS("a", 8)
    b = claripy.BVS("b", 8)
    x = claripy.BVS("x", 32)
    y = claripy.BVS("y", 32)
    z = claripy.BVS("z", 32)

    xy = x + y
    dst = claripy.BVV(0xbaaaaf50, 32) + xy
    constraints = [ ]
    constraints.append(x <= 0x1)
    constraints.append(x != 0x0)
    constraints.append(claripy.SignExt(24, claripy.If(x > 0x0, a, 0)) != 0xa)
    constraints.append(x < 0x80)
    constraints.append(y <= 0x1)
    constraints.append(x == 0x1)
    constraints.append((0xbaaaaf50 + x) == 0xbaaaaf51)
    constraints.append(y != 0x0)
    constraints.append(claripy.SignExt(24, claripy.If(y > 0x0, b, 0)) != 0xa)
    constraints.append((x + y) < 0x80)
    constraints.append(z <= 0x1)
    constraints.append((x + y) == 0x2)

    sn = claripy.Solver()
    sc = claripy.SolverComposite()

    sn.add(constraints)
    sc.add(constraints)
    print sn.max(dst), sc.max(dst)
    print sn.min(dst), sc.min(dst)
    assert sn.max(dst) == sc.max(dst)
    assert sn.min(dst) == sc.min(dst)

def test_model():
    x = claripy.BVS("x", 32)
    y = claripy.BVS("y", 32)
    s = claripy.Solver()

    s.add(x < 10)
    assert sorted(s.eval(x, 20)) == range(10)
    s.add(y == 1337)
    assert sorted(s.eval(x, 20)) == range(10)

def test_unsatness():
    x = claripy.BVS("x", 32)

    s = claripy.Solver()
    s.add(x == 10)
    assert s.satisfiable()
    s.add(claripy.false)
    assert not s.satisfiable()

def test_simplification_annotations():
    s = claripy.Solver()
    x = claripy.BVS("x", 32)

    s.add(x > 10)
    s.add(x > 11)
    s.add((x > 12).annotate(claripy.SimplificationAvoidanceAnnotation()))

    assert len(s.constraints) == 3
    s.simplify()
    assert len(s.constraints) == 2

if __name__ == '__main__':
    test_simplification_annotations()
    test_model()
    test_composite_discrepancy()
    for func, param in test_solver():
        func(param)
    test_hybrid_solver()
    test_replacement_solver()
    test_minmax()
    test_solver_branching()
    for func, param in test_solver_branching():
        func(param)
    for func, param in test_combine():
        func(param)
    test_composite_solver()
