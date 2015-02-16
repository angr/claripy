import sys
import pickle
import tempfile

import nose
import logging
l = logging.getLogger("claripy.test")

#import tempfile
import claripy
import ana

try: import claripy_logging #pylint:disable=import-error,unused-import
except ImportError: pass

def test_expression():
    clrp = claripy.Claripies["SerialZ3"]
    bc = clrp.backend_of_type(claripy.backends.BackendConcrete)

    e = clrp.BitVecVal(0x01020304, 32)
    nose.tools.assert_equal(len(e), 32)
    r = e.reversed
    nose.tools.assert_equal(r.resolved_with(bc), 0x04030201)
    nose.tools.assert_equal(len(r), 32)

    nose.tools.assert_equal([ i.model for i in r.chop(8) ], [ 4, 3, 2, 1 ] )

    e1 = r[31:24]
    nose.tools.assert_equal(e1.model, 0x04)
    nose.tools.assert_equal(len(e1), 8)
    nose.tools.assert_equal(e1[2].model, 1)
    nose.tools.assert_equal(e1[1].model, 0)

    ee1 = e1.zero_extend(8)
    nose.tools.assert_equal(ee1.model, 0x0004)
    nose.tools.assert_equal(len(ee1), 16)

    ee1 = clrp.BitVecVal(0xfe, 8).sign_extend(8)
    nose.tools.assert_equal(ee1.model, 0xfffe)
    nose.tools.assert_equal(len(ee1), 16)

    xe1 = [ i.model for i in e1.chop(1) ]
    nose.tools.assert_equal(xe1, [ 0, 0, 0, 0, 0, 1, 0, 0 ])

    a = clrp.BitVecVal(1, 1)
    nose.tools.assert_equal((a+a).model, 2)

    x = clrp.BitVecVal(1, 32)
    nose.tools.assert_equal(x.length, 32)
    y = clrp.LShR(x, 10)
    nose.tools.assert_equal(y.length, 32)

    r = clrp.BitVecVal(0x01020304, 32)
    rr = r.reversed
    rrr = rr.reversed
    nose.tools.assert_is(r.model, rrr.model)
    #nose.tools.assert_is(type(rr.model), claripy.A)
    nose.tools.assert_equal(rr.resolved_with(bc), 0x04030201)

    rsum = r+rr
    nose.tools.assert_equal(rsum.model, 0x05050505)

    # test identity
    nose.tools.assert_true(r.identical(rrr))
    nose.tools.assert_false(r.identical(rr))
    ii = clrp.BitVec('ii', 32)
    ij = clrp.BitVec('ij', 32)
    nose.tools.assert_true(ii.identical(ii))
    nose.tools.assert_false(ii.identical(ij))

    clrp_vsa = claripy.Claripies['VSA']
    si = clrp_vsa.StridedInterval(bits=32, stride=0, lower_bound=20, upper_bound=100)
    sj = clrp_vsa.StridedInterval(bits=32, stride=0, lower_bound=10, upper_bound=10)
    sk = clrp_vsa.StridedInterval(bits=32, stride=0, lower_bound=20, upper_bound=100)
    nose.tools.assert_true(si.identical(si))
    nose.tools.assert_false(si.identical(sj))
    nose.tools.assert_true(si.identical(sk))

    # test hash cache
    nose.tools.assert_is(a+a, a+a)

    # test replacement
    old = clrp.BitVec('old', 32, explicit_name=True)
    new = clrp.BitVec('new', 32, explicit_name=True)
    ooo = clrp.BitVecVal(0, 32)

    old_formula = clrp.If((old + 1)%256 == 0, old+10, old+20)
    new_formula = old_formula.replace(old, new)
    ooo_formula = new_formula.replace(new, ooo)

    nose.tools.assert_not_equal(hash(old_formula), hash(new_formula))
    nose.tools.assert_not_equal(hash(old_formula), hash(ooo_formula))
    nose.tools.assert_not_equal(hash(new_formula), hash(ooo_formula))

    nose.tools.assert_equal(old_formula.variables, { 'old' })
    nose.tools.assert_equal(new_formula.variables, { 'new' })
    nose.tools.assert_equal(ooo_formula.variables, set())

    nose.tools.assert_true(old_formula.symbolic)
    nose.tools.assert_true(new_formula.symbolic)
    nose.tools.assert_true(new_formula.symbolic)

    nose.tools.assert_equal(str(old_formula).replace('old', 'new'), str(new_formula))
    nose.tools.assert_equal(ooo_formula.model, 20)

    # test AST collapse
    s = clrp_vsa.SI(bits=32, stride=0, lower_bound=10, upper_bound=10)
    b = clrp_vsa.BVV(20, 32)

    sb = s+b
    nose.tools.assert_true(isinstance(sb.args[0], claripy.A))

    bb = b+b
    nose.tools.assert_false(isinstance(bb.args[0], claripy.A))

    ss = s+s
    nose.tools.assert_false(isinstance(ss.args[0], claripy.A))

    sob = s|b
    # for now, this is collapsed. Presumably, Fish will make it not collapse at some point
    nose.tools.assert_true(isinstance(sob.args[0], claripy.A))

    # make sure the AST collapses for delayed ops like reversing
    rb = b.reversed
    nose.tools.assert_true(isinstance(rb.args[0], claripy.A))

    rbi = rb.identical(bb)
    nose.tools.assert_is(rbi, False)

    rbi = rb.identical(rb)
    nose.tools.assert_is(rbi, True)

def test_concrete():
    clrp = claripy.Claripies["SerialZ3"]

    a = clrp.BitVecVal(10, 32)
    b = clrp.BoolVal(True)
    c = clrp.BitVec('x', 32)

    nose.tools.assert_is(type(a.model), claripy.BVV)
    nose.tools.assert_is(type(b.model), bool)
    nose.tools.assert_is(type(c.model), claripy.A)

def test_fallback_abstraction():
    clrp = claripy.Claripies["SerialZ3"]
    bz = clrp.backend_of_type(claripy.backends.BackendZ3)

    a = clrp.BitVecVal(5, 32)
    b = clrp.BitVec('x', 32, explicit_name=True)
    c = a+b
    d = 5+b
    e = b+5
    f = b+b
    g = a+a

    nose.tools.assert_false(a.symbolic)
    nose.tools.assert_true(b.symbolic)
    nose.tools.assert_true(c.symbolic)
    nose.tools.assert_true(d.symbolic)
    nose.tools.assert_true(e.symbolic)
    nose.tools.assert_true(f.symbolic)

    nose.tools.assert_is(type(a.model), claripy.BVV)
    nose.tools.assert_is(type(b.model), claripy.A)
    nose.tools.assert_is(type(c.model), claripy.A)
    nose.tools.assert_is(type(d.model), claripy.A)
    nose.tools.assert_is(type(e.model), claripy.A)
    nose.tools.assert_is(type(f.model), claripy.A)
    nose.tools.assert_is(type(g.model), claripy.BVV)

    nose.tools.assert_equal(str(b.resolved_with(bz)), 'x')
    nose.tools.assert_equal(b.resolved_with(bz).__module__, 'z3')

    nose.tools.assert_equal(str(c.resolved_with(bz)), '5 + x')
    nose.tools.assert_equal(str(d.resolved_with(bz)), '5 + x')
    nose.tools.assert_equal(str(e.resolved_with(bz)), 'x + 5')
    nose.tools.assert_equal(str(f.resolved_with(bz)), 'x + x')

def test_pickle():
    clrp = claripy.Claripies['SerialZ3']
    bz = clrp.backend_of_type(claripy.backends.BackendZ3)

    a = clrp.BitVecVal(0, 32)
    b = clrp.BitVec('x', 32, explicit_name=True)

    c = a+b
    nose.tools.assert_equal(c.resolved_with(bz).__module__, 'z3')
    nose.tools.assert_equal(str(c.resolved_with(bz)), '0 + x')

    c_copy = pickle.loads(pickle.dumps(c, -1))
    nose.tools.assert_equal(c_copy.resolved_with(bz).__module__, 'z3')
    nose.tools.assert_equal(str(c_copy.resolved_with(bz)), '0 + x')

def test_datalayer():
    l.info("Running test_datalayer")

    clrp = claripy.Claripies['SerialZ3']
    pickle_dir = tempfile.mkdtemp()
    ana.set_dl(pickle_dir=pickle_dir)
    l.debug("Pickling to %s",pickle_dir)

    a = clrp.BitVecVal(0, 32)
    b = clrp.BitVec("x", 32)
    c = a + b
    d = a+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b

    l.debug("Storing!")
    a.ana_store()
    c_info = c.ana_store()
    d_info = d.ana_store()

    l.debug("Loading!")
    ana.set_dl(pickle_dir=pickle_dir)
    #nose.tools.assert_equal(len(clrp.dl._cache), 0)

    cc = claripy.A.ana_load(c_info)
    nose.tools.assert_equal(str(cc), str(c))
    cd = claripy.A.ana_load(d_info)
    nose.tools.assert_equal(str(cd), str(d))

    l.debug("Time to test some solvers!")
    s = clrp.solver()
    x = clrp.BitVec("x", 32)
    s.add(x == 3)
    s.finalize()
    ss = claripy.solvers.Solver.ana_load(s.ana_store())
    nose.tools.assert_equal(str(s.constraints), str(ss.constraints))
    nose.tools.assert_equal(str(s.variables), str(ss.variables))

    s = clrp.composite_solver()
    x = clrp.BitVec("x", 32)
    s.add(x == 3)
    s.finalize()
    ss = claripy.solvers.CompositeSolver.ana_load(s.ana_store())
    old_constraint_sets = [[hash(j) for j in k.constraints] for k in s._solver_list]
    new_constraint_sets = [[hash(j) for j in k.constraints] for k in ss._solver_list]
    nose.tools.assert_items_equal(old_constraint_sets, new_constraint_sets)
    nose.tools.assert_equal(str(s.variables), str(ss.variables))


def test_model():
    clrp = claripy.Claripies["SerialZ3"]
    bc = clrp.backend_of_type(claripy.backends.BackendConcrete)

    a = clrp.BitVecVal(5, 32)
    b = clrp.BitVec('x', 32, explicit_name=True)
    c = a + b

    r_c = c.resolved_with(bc, result=claripy.Result(True, {'x': 10}))
    nose.tools.assert_equal(r_c, 15)
    r_d = c.resolved_with(bc, result=claripy.Result(True, {'x': 15}))
    nose.tools.assert_equal(r_c, 15)
    nose.tools.assert_equal(r_d, 20)

def test_solver():
    raw_solver(claripy.solvers.BranchingSolver)
    raw_solver(claripy.solvers.CompositeSolver)
def raw_solver(solver_type):
    clrp = claripy.Claripies["SerialZ3"]
    #bc = claripy.backends.BackendConcrete(clrp)
    #bz = claripy.backends.BackendZ3(clrp)
    #clrp.expression_backends = [ bc, bz, ba ]

    s = solver_type(clrp)

    s.simplify()

    x = clrp.BitVec('x', 32)
    y = clrp.BitVec('y', 32)
    z = clrp.BitVec('z', 32)

    l.debug("adding constraints")

    s.add(x == 10)
    s.add(y == 15)
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
    nose.tools.assert_equal({ len(shards[0].constraints), len(shards[1].constraints) }, { 1, 1 }) # adds the != from the solution() check

    s = solver_type(clrp)
    #clrp.expression_backends = [ bc, ba, bz ]
    s.add(clrp.UGT(x, 10))
    s.add(clrp.UGT(x, 20))
    s.simplify()
    nose.tools.assert_equal(len(s.constraints), 1)
    #nose.tools.assert_equal(str(s.constraints[0]._obj), "Not(ULE(x <= 20))")

    s.add(clrp.UGT(y, x))
    s.add(clrp.ULT(z, 5))

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

    nose.tools.assert_equal(s.max(z), 4)
    nose.tools.assert_equal(s.min(z), 0)
    nose.tools.assert_equal(s.min(y), 22)
    nose.tools.assert_equal(s.max(y), 2**y.size()-1)

    ss = s.split()
    nose.tools.assert_equal(len(ss), 2)
    if type(s) is claripy.solvers.BranchingSolver:
        nose.tools.assert_equal({ len(_.constraints) for _ in ss }, { 2, 3 }) # constraints from min or max
    elif type(s) is claripy.solvers.CompositeSolver:
        nose.tools.assert_equal({ len(_.constraints) for _ in ss }, { 3, 3 }) # constraints from min or max

    # test that False makes it unsat
    s = solver_type(clrp)
    s.add(clrp.BitVecVal(1,1) == clrp.BitVecVal(1,1))
    nose.tools.assert_true(s.satisfiable())
    s.add(clrp.BitVecVal(1,1) == clrp.BitVecVal(0,1))
    nose.tools.assert_false(s.satisfiable())

    # test extra constraints
    s = solver_type(clrp)
    x = clrp.BitVec('x', 32)
    nose.tools.assert_equal(s.eval(x, 2, extra_constraints=[x==10]), ( 10, ))
    s.add(x == 10)
    nose.tools.assert_false(s.solution(x, 2))
    nose.tools.assert_true(s.solution(x, 10))

    # test result caching

    s = solver_type(clrp)
    nose.tools.assert_true(s.satisfiable())
    s.add(clrp.BoolVal(False))
    nose.tools.assert_false(s.satisfiable())
    s._result = None
    nose.tools.assert_false(s.satisfiable())

def test_solver_branching():
    raw_solver_branching(claripy.solvers.BranchingSolver)
    raw_solver_branching(claripy.solvers.CompositeSolver)
def raw_solver_branching(solver_type):
    clrp = claripy.Claripies["SerialZ3"]
    s = solver_type(clrp)
    x = clrp.BitVec("x", 32)
    y = clrp.BitVec("y", 32)
    s.add(x > y)
    s.add(x < 10)

    nose.tools.assert_equals(s.eval(x, 1)[0], 1)

    t = s.branch()
    if type(s) is claripy.solvers.BranchingSolver:
        nose.tools.assert_is(s._solver_states.values()[0], t._solver_states.values()[0])
        nose.tools.assert_true(s._finalized)
        nose.tools.assert_true(t._finalized)
    t.add(x > 5)
    if type(s) is claripy.solvers.BranchingSolver:
        nose.tools.assert_equal(len(t._solver_states), 0)

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
    raw_combine(claripy.solvers.BranchingSolver)
    raw_combine(claripy.solvers.CompositeSolver)
def raw_combine(solver_type):
    clrp = claripy.Claripies["SerialZ3"]
    s10 = solver_type(clrp)
    s20 = solver_type(clrp)
    s30 = solver_type(clrp)
    x = clrp.BitVec("x", 32)

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
    nose.tools.assert_equal(s30.combine([s10]).eval(x, 1), ( 30, ))
    nose.tools.assert_equal(len(s30.combine([s10]).constraints), 2)

def test_bv():
    claripy.bv.test()

def test_simple_merging():
    raw_simple_merging(claripy.solvers.BranchingSolver)
    raw_simple_merging(claripy.solvers.CompositeSolver)
def raw_simple_merging(solver_type):
    clrp = claripy.Claripies["SerialZ3"]
    s1 = solver_type(clrp)
    s2 = solver_type(clrp)
    w = clrp.BitVec("w", 8)
    x = clrp.BitVec("x", 8)
    y = clrp.BitVec("y", 8)
    z = clrp.BitVec("z", 8)
    m = clrp.BitVec("m", 8)

    s1.add([x == 1, y == 10])
    s2.add([x == 2, z == 20, w == 5])
    _, sm = s1.merge([s2], m, [ 0, 1 ])

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

    m2 = clrp.BitVec("m2", 32)
    _, smm = sm1.merge([sm2], m2, [0, 1])

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

    so = solver_type(clrp)
    so.add(w == 0)

    sa = so.branch()
    sb = so.branch()
    sa.add(x == 1)
    sb.add(x == 2)
    _, sm = sa.merge([sb], m, [0, 1])

    smc = sm.branch()
    smd = sm.branch()
    smc.add(y == 3)
    smd.add(y == 4)

    _, smm = smc.merge([smd], m2, [0, 1])
    wxy = clrp.Concat(w, x, y)

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

def test_composite_solver():
    clrp = claripy.Claripies["SerialZ3"]
    s = clrp.composite_solver()
    x = clrp.BitVec("x", 32)
    y = clrp.BitVec("y", 32)
    z = clrp.BitVec("z", 32)
    c = clrp.And(x == 1, y == 2, z == 3)
    s.add(c)
    nose.tools.assert_equals(len(s._solver_list), 4) # including the CONSTANT solver
    nose.tools.assert_true(s.satisfiable())

    s.add(x < y)
    nose.tools.assert_equal(len(s._solver_list), 3)
    nose.tools.assert_true(s.satisfiable())

    s.simplify()
    nose.tools.assert_equal(len(s._solver_list), 4)
    nose.tools.assert_true(s.satisfiable())

    s1 = s.branch()
    s1.add(x > y)
    nose.tools.assert_equal(len(s1._solver_list), 3)
    nose.tools.assert_false(s1.satisfiable())
    nose.tools.assert_equal(len(s._solver_list), 4)
    nose.tools.assert_true(s.satisfiable())

    s.add(clrp.BitVecVal(1, 32) == clrp.BitVecVal(2, 32))
    nose.tools.assert_equal(len(s._solver_list), 4) # the CONCRETE one
    nose.tools.assert_false(s.satisfiable())

def test_ite():
    raw_ite(claripy.solvers.BranchingSolver)
    raw_ite(claripy.solvers.CompositeSolver)
def raw_ite(solver_type):
    clrp = claripy.Claripies["SerialZ3"]
    s = solver_type(clrp)
    x = clrp.BitVec("x", 32)
    y = clrp.BitVec("y", 32)
    z = clrp.BitVec("z", 32)

    ite = clrp.ite_dict(x, {1:11, 2:22, 3:33, 4:44, 5:55, 6:66, 7:77, 8:88, 9:99}, clrp.BitVecVal(0, 32))
    nose.tools.assert_equal(sorted(s.eval(ite, 100)), [ 0, 11, 22, 33, 44, 55, 66, 77, 88, 99 ] )

    ss = s.branch()
    ss.add(ite == 88)
    nose.tools.assert_equal(sorted(ss.eval(ite, 100)), [ 88 ] )
    nose.tools.assert_equal(sorted(ss.eval(x, 100)), [ 8 ] )

    ity = clrp.ite_dict(x, {1:11, 2:22, 3:y, 4:44, 5:55, 6:66, 7:77, 8:88, 9:99}, clrp.BitVecVal(0, 32))
    ss = s.branch()
    ss.add(ity != 11)
    ss.add(ity != 22)
    ss.add(ity != 33)
    ss.add(ity != 44)
    ss.add(ity != 55)
    ss.add(ity != 66)
    ss.add(ity != 77)
    ss.add(ity != 88)
    ss.add(ity != 0)
    ss.add(y == 123)
    nose.tools.assert_equal(sorted(ss.eval(ity, 100)), [ 99, 123 ] )
    nose.tools.assert_equal(sorted(ss.eval(x, 100)), [ 3, 9 ] )
    nose.tools.assert_equal(sorted(ss.eval(y, 100)), [ 123 ] )

    itz = clrp.ite_cases([ (clrp.And(x == 10, y == 20), 33), (clrp.And(x==1, y==2), 3), (clrp.And(x==100, y==200), 333) ], clrp.BitVecVal(0, 32))
    ss = s.branch()
    ss.add(z == itz)
    ss.add(itz != 0)
    nose.tools.assert_equal(ss.eval(y/x, 100), ( 2, ))
    nose.tools.assert_items_equal(sorted([ b.value for b in ss.eval(x, 100) ]), ( 1, 10, 100 ))
    nose.tools.assert_items_equal(sorted([ b.value for b in ss.eval(y, 100) ]), ( 2, 20, 200 ))

def test_bool():
    clrp = claripy.Claripies["SerialZ3"]
    bc = clrp.backend_of_type(claripy.backends.BackendConcrete)

    a = clrp.And(*[False, False, True])
    nose.tools.assert_equal(a.resolved_with(bc), False)
    a = clrp.And(*[True, True, True])
    nose.tools.assert_equal(a.resolved_with(bc), True)

    o = clrp.Or(*[False, False, True])
    nose.tools.assert_equal(o.resolved_with(bc), True)
    o = clrp.Or(*[False, False, False])
    nose.tools.assert_equal(o.resolved_with(bc), False)

def broken_vsa():
    from claripy.backends import BackendVSA
    from claripy.vsa import TrueResult, FalseResult, MaybeResult #pylint:disable=unused-variable

    clrp = claripy.Claripies["SerialZ3"]
    # Set backend
    b = BackendVSA()
    b.set_claripy_object(clrp)
    clrp.model_backends.append(b)

    solver_type = claripy.solvers.BranchingSolver
    s = solver_type(clrp) #pylint:disable=unused-variable

    # Integers
    si1 = clrp.StridedInterval(bits=32, stride=0, lower_bound=10, upper_bound=10)
    si2 = clrp.StridedInterval(bits=32, stride=0, lower_bound=10, upper_bound=10)
    si3 = clrp.StridedInterval(bits=32, stride=0, lower_bound=28, upper_bound=28)
    # Strided intervals
    si_a = clrp.StridedInterval(bits=32, stride=2, lower_bound=10, upper_bound=20)
    si_b = clrp.StridedInterval(bits=32, stride=2, lower_bound=-100, upper_bound=200)
    si_c = clrp.StridedInterval(bits=32, stride=3, lower_bound=-100, upper_bound=200)
    si_d = clrp.StridedInterval(bits=32, stride=2, lower_bound=50, upper_bound=60)
    si_e = clrp.StridedInterval(bits=16, stride=1, lower_bound=0x2000, upper_bound=0x3000)
    si_f = clrp.StridedInterval(bits=16, stride=1, lower_bound=0, upper_bound=255)
    si_g = clrp.StridedInterval(bits=16, stride=1, lower_bound=0, upper_bound=0xff)
    si_h = clrp.StridedInterval(bits=32, stride=0, lower_bound=0x80000000, upper_bound=0x80000000)
    nose.tools.assert_equal(si1.model == 10, TrueResult())
    nose.tools.assert_equal(si2.model == 10, TrueResult())
    nose.tools.assert_equal(si1.model == si2.model, TrueResult())
    # __add__
    si_add_1 = b.convert((si1 + si2))
    nose.tools.assert_equal(si_add_1 == 20, TrueResult())
    si_add_2 = b.convert((si1 + si_a))
    nose.tools.assert_equal(si_add_2 == clrp.StridedInterval(bits=32, stride=2, lower_bound=20, upper_bound=30).model, TrueResult())
    si_add_3 = b.convert((si_a + si_b))
    nose.tools.assert_equal(si_add_3 == clrp.StridedInterval(bits=32, stride=2, lower_bound=-90, upper_bound=220).model, TrueResult())
    si_add_4 = b.convert((si_b + si_c))
    nose.tools.assert_equal(si_add_4 == clrp.StridedInterval(bits=32, stride=1, lower_bound=-200, upper_bound=400).model, TrueResult())
    # __add__ with overflow
    si_add_5 = b.convert(si_h + 0xffffffff)
    nose.tools.assert_equal(si_add_5 == clrp.StridedInterval(bits=32, stride=0, lower_bound=0x7fffffff, upper_bound=0x7fffffff).model, TrueResult())
    # __sub__
    si_minus_1 = b.convert((si1 - si2))
    nose.tools.assert_equal(si_minus_1 == 0, TrueResult())
    si_minus_2 = b.convert((si_a - si_b))
    nose.tools.assert_equal(si_minus_2 == clrp.StridedInterval(bits=32, stride=2, lower_bound=-190, upper_bound=120).model, TrueResult())
    si_minus_3 = b.convert((si_b - si_c))
    nose.tools.assert_equal(si_minus_3 == clrp.StridedInterval(bits=32, stride=1, lower_bound=-300, upper_bound=300).model, TrueResult())
    # __neg__ / __invert__
    si_neg_1 = b.convert((~si1))
    nose.tools.assert_equal(si_neg_1 == -11, TrueResult())
    si_neg_2 = b.convert((~si_b))
    nose.tools.assert_equal(si_neg_2 == clrp.StridedInterval(bits=32, stride=2, lower_bound=-201, upper_bound=99).model, TrueResult())
    # __or__
    si_or_1 = b.convert(si1 | si3)
    nose.tools.assert_equal(si_or_1 == 30, TrueResult())
    si_or_2 = b.convert(si1 | si2)
    nose.tools.assert_equal(si_or_2 == 10, TrueResult())
    si_or_3 = b.convert(si1 | si_a) # An integer | a strided interval
    nose.tools.assert_equal(si_or_3 == clrp.StridedInterval(bits=32, stride=2, lower_bound=10, upper_bound=30).model, TrueResult())
    si_or_3 = b.convert(si_a | si1) # Exchange the operands
    nose.tools.assert_equal(si_or_3 == clrp.StridedInterval(bits=32, stride=2, lower_bound=10, upper_bound=30).model, TrueResult())
    si_or_4 = b.convert(si_a | si_d) # A strided interval | another strided interval
    nose.tools.assert_equal(si_or_4 == clrp.StridedInterval(bits=32, stride=2, lower_bound=50, upper_bound=62).model, TrueResult())
    si_or_4 = b.convert(si_d | si_a) # Exchange the operands
    nose.tools.assert_equal(si_or_4 == clrp.StridedInterval(bits=32, stride=2, lower_bound=50, upper_bound=62).model, TrueResult())
    si_or_5 = b.convert(si_e | si_f) #
    nose.tools.assert_equal(si_or_5 == clrp.StridedInterval(bits=16, stride=1, lower_bound=0x2000, upper_bound=0x30ff).model, TrueResult())
    si_or_6 = b.convert(si_e | si_g) #
    nose.tools.assert_equal(si_or_6 == clrp.StridedInterval(bits=16, stride=1, lower_bound=0x2000, upper_bound=0x30ff).model, TrueResult())
    # Shifting
    si_shl_1 = b.convert(si1 << 3)
    nose.tools.assert_equal(si_shl_1.bits, 32)
    nose.tools.assert_equal(si_shl_1 == clrp.StridedInterval(bits=32, stride=0, lower_bound=80, upper_bound=80).model, TrueResult())

    # Extracting an integer
    si = clrp.StridedInterval(bits=64, stride=0, lower_bound=0x7fffffffffff0000, upper_bound=0x7fffffffffff0000)
    part1 = b.convert(si[63 : 32])
    part2 = b.convert(si[31 : 0])
    nose.tools.assert_equal(part1 == clrp.StridedInterval(bits=32, stride=0, lower_bound=0x7fffffff, upper_bound=0x7fffffff).model, TrueResult())
    nose.tools.assert_equal(part2 == clrp.StridedInterval(bits=32, stride=0, lower_bound=0xffff0000, upper_bound=0xffff0000).model, TrueResult())

    # Concatenating two integers
    si_concat = b.convert(part1.concat(part2))
    nose.tools.assert_equal(si_concat == si.model, TrueResult())

    # Extracting a SI
    si = clrp.SI(bits=64, stride=0x9, lower_bound=0x1, upper_bound=0xa)
    part1 = b.convert(si[63 : 32])
    part2 = b.convert(si[31 : 0])
    nose.tools.assert_equal(part1 == clrp.SI(bits=32, stride=0, lower_bound=0x0, upper_bound=0x0).model, TrueResult())
    nose.tools.assert_equal(part2 == clrp.SI(bits=32, stride=9, lower_bound=1, upper_bound=10).model, TrueResult())

    # Concatenating two SIs
    si_concat = b.convert(part1.concat(part2))
    nose.tools.assert_equal(si_concat == si.model, TrueResult())

    # Zero-Extend the low part
    si_zeroextended = b.convert(part2.zero_extend(32))
    nose.tools.assert_equal(si_zeroextended == clrp.SI(bits=64, stride=9, lower_bound=1, upper_bound=10).model, TrueResult())

    # Extract from the result above
    si_extracted = b.convert(si_zeroextended.extract(31, 0))
    nose.tools.assert_equal(si_extracted == clrp.SI(bits=32, stride=9, lower_bound=1, upper_bound=10).model, TrueResult())

    # Union
    si_union_1 = b.convert(si1.union(si2))
    nose.tools.assert_equal(si_union_1 == clrp.StridedInterval(bits=32, stride=0, lower_bound=10, upper_bound=10).model, TrueResult())
    si_union_2 = b.convert(si1.union(si3))
    nose.tools.assert_equal(si_union_2 == clrp.StridedInterval(bits=32, stride=18, lower_bound=10, upper_bound=28).model, TrueResult())
    si_union_3 = b.convert(si1.union(si_a))
    nose.tools.assert_equal(si_union_3 == clrp.StridedInterval(bits=32, stride=2, lower_bound=10, upper_bound=20).model, TrueResult())
    si_union_4 = b.convert(si_a.union(si_b))
    nose.tools.assert_equal(si_union_4 == clrp.StridedInterval(bits=32, stride=2, lower_bound=-100, upper_bound=200).model, TrueResult())
    si_union_5 = b.convert(si_b.union(si_c))
    nose.tools.assert_equal(si_union_5 == clrp.StridedInterval(bits=32, stride=1, lower_bound=-100, upper_bound=200).model, TrueResult())

    # Intersection
    si_intersection_1 = b.convert(si1.intersection(si1))
    nose.tools.assert_equal(si_intersection_1 == si2, TrueResult())
    si_intersection_2 = b.convert(si1.intersection(si2))
    nose.tools.assert_equal(si_intersection_2 == clrp.StridedInterval(bits=32, stride=0, lower_bound=10, upper_bound=10).model, TrueResult())
    si_intersection_3 = b.convert(si1.intersection(si_a))
    nose.tools.assert_equal(si_intersection_3 == clrp.StridedInterval(bits=32, stride=0, lower_bound=10, upper_bound=10).model, TrueResult())
    si_intersection_4 = b.convert(si_a.intersection(si_b))
    nose.tools.assert_equal(si_intersection_4 == clrp.StridedInterval(bits=32, stride=2, lower_bound=10, upper_bound=20).model, TrueResult())
    si_intersection_5 = b.convert(si_b.intersection(si_c))
    nose.tools.assert_equal(si_intersection_5 == clrp.StridedInterval(bits=32, stride=6, lower_bound=-100, upper_bound=200).model, TrueResult())

    # ValueSet
    vs_1 = clrp.ValueSet()
    nose.tools.assert_true(vs_1.model.is_empty(), True)
    # Test merging two addresses
    vs_1.model.merge_si('global', si1)
    vs_1.model.merge_si('global', si3)
    nose.tools.assert_equal(vs_1.model.get_si('global') == clrp.StridedInterval(bits=32, stride=18, lower_bound=10, upper_bound=28).model, TrueResult())
    # Length of this ValueSet
    nose.tools.assert_equal(len(vs_1.model), 32)

if __name__ == '__main__':
    logging.getLogger('claripy.test').setLevel(logging.DEBUG)
    logging.getLogger('claripy.claripy').setLevel(logging.DEBUG)
    logging.getLogger('claripy.ast').setLevel(logging.DEBUG)
    logging.getLogger('claripy.expression').setLevel(logging.DEBUG)
    logging.getLogger('claripy.backends.backend').setLevel(logging.DEBUG)
    logging.getLogger('claripy.backends.backend_concrete').setLevel(logging.DEBUG)
    logging.getLogger('claripy.backends.backend_abstract').setLevel(logging.DEBUG)
    logging.getLogger('claripy.backends.backend_z3').setLevel(logging.DEBUG)
    logging.getLogger('claripy.datalayer').setLevel(logging.DEBUG)
    logging.getLogger('claripy.solvers.solver').setLevel(logging.DEBUG)
    logging.getLogger('claripy.solvers.core_solver').setLevel(logging.DEBUG)
    logging.getLogger('claripy.solvers.branching_solver').setLevel(logging.DEBUG)
    logging.getLogger('claripy.solvers.composite_solver').setLevel(logging.DEBUG)

    if len(sys.argv) > 1:
        globals()['test_' + sys.argv[1]]()
    else:
        # test other stuff as well
        test_expression()
        test_fallback_abstraction()
        test_pickle()
        test_datalayer()
        test_model()
        test_solver()
        test_solver_branching()
        test_combine()
        test_bv()
        test_simple_merging()
        test_composite_solver()
        test_ite()
        test_bool()
        #test_vsa()
    print "WOO"

    print 'eval', claripy.solvers.solver.cached_evals
    print 'min', claripy.solvers.solver.cached_min
    print 'max', claripy.solvers.solver.cached_max
    print 'solve', claripy.solvers.solver.cached_solve
