import sys
import pickle
import tempfile

import nose.tools
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
    rrr = rr.reversed.simplified
    #nose.tools.assert_is(r.model, rrr.model)
    #nose.tools.assert_is(type(rr.model), claripy.A)
    nose.tools.assert_equal(rr.resolved_with(bc), 0x04030201)
    nose.tools.assert_is(r.concat(rr), clrp.Concat(r, rr))

    rsum = r+rr
    nose.tools.assert_equal(rsum.model, 0x05050505)

    r = clrp.BitVec('x', 32)
    rr = r.reversed
    rrr = rr.reversed
    nose.tools.assert_is(r, rrr)

    # test identity
    nose.tools.assert_true(r.identical(rrr))
    nose.tools.assert_false(r.identical(rr))
    ii = clrp.BitVec('ii', 32)
    ij = clrp.BitVec('ij', 32)
    nose.tools.assert_true(ii.identical(ii))
    nose.tools.assert_false(ii.identical(ij))

    clrp_vsa = claripy.Claripies['VSA']
    si = clrp_vsa.StridedInterval(bits=32, stride=2, lower_bound=20, upper_bound=100)
    sj = clrp_vsa.StridedInterval(bits=32, stride=2, lower_bound=10, upper_bound=10)
    sk = clrp_vsa.StridedInterval(bits=32, stride=2, lower_bound=20, upper_bound=100)
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
    nose.tools.assert_equal(ooo_formula.variables, ooo.variables)

    nose.tools.assert_true(old_formula.symbolic)
    nose.tools.assert_true(new_formula.symbolic)
    nose.tools.assert_true(new_formula.symbolic)

    nose.tools.assert_equal(str(old_formula).replace('old', 'new'), str(new_formula))
    nose.tools.assert_equal(ooo_formula.model, 20)

    # test AST collapse
    s = clrp_vsa.SI(bits=32, stride=0, lower_bound=10, upper_bound=10)
    b = clrp_vsa.BVV(20, 32)

    sb = s+b
    nose.tools.assert_is_instance(sb.args[0], claripy.Base)

    bb = b+b
    # this was broken previously -- it was checking if type(bb.args[0]) == A,
    # and it wasn't, but was instead a subclass. leaving this out for now
    # nose.tools.assert_not_is_instance(bb.args[0], claripy.Base)

    ss = s+s
    # (see above)
    # nose.tools.assert_not_is_instance(ss.args[0], claripy.Base)

    sob = s|b
    # for now, this is collapsed. Presumably, Fish will make it not collapse at some point
    nose.tools.assert_is_instance(sob.args[0], claripy.Base)

    # make sure the AST collapses for delayed ops like reversing
    rb = b.reversed
    #nose.tools.assert_is_instance(rb.args[0], claripy.Base)
    # TODO: Properly delay reversing: should not be eager

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
    nose.tools.assert_is_instance(c.model, claripy.Base)

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
    nose.tools.assert_is_instance(b.model, claripy.Base)
    nose.tools.assert_is_instance(c.model, claripy.Base)
    nose.tools.assert_is_instance(d.model, claripy.Base)
    nose.tools.assert_is_instance(e.model, claripy.Base)
    nose.tools.assert_is_instance(f.model, claripy.Base)
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

    cc = claripy.BV.ana_load(c_info)
    nose.tools.assert_equal(str(cc), str(c))
    cd = claripy.BV.ana_load(d_info)
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
    s.add(clrp.UGT(x, y))
    s.add(clrp.ULT(x, 10))

    nose.tools.assert_greater(s.eval(x, 1)[0], 0)

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

def test_wrapped_intervals():
    from claripy.backends import BackendVSA

    clrp = claripy.Claripies["SerialZ3"]
    # Set backend
    b = BackendVSA()
    b.set_claripy_object(clrp)
    clrp.model_backends.append(b)
    clrp.solver_backends = []

    solver_type = claripy.solvers.BranchingSolver
    s = solver_type(clrp)  # pylint:disable=unused-variable

    SI = clrp.StridedInterval
    VS = clrp.ValueSet
    BVV = clrp.BVV

    # Disable the use of DiscreteStridedIntervalSet
    claripy.vsa.strided_interval.allow_dsis = False

    # Plain addition
    si1 = SI(bits=32, stride=1, lower_bound=-1, upper_bound=1)
    si2 = SI(bits=32, stride=1, lower_bound=-1, upper_bound=1)
    si3 = SI(bits=32, stride=1, lower_bound=-2, upper_bound=2)
    nose.tools.assert_true((si1 + si2).ExactEQ(si3).model)
    si4 = SI(bits=32, stride=1, lower_bound=0xfffffffe, upper_bound=2)
    nose.tools.assert_true((si1 + si2).ExactEQ(si4).model)
    si5 = SI(bits=32, stride=1, lower_bound=2, upper_bound=-2)
    nose.tools.assert_false((si1 + si2).ExactEQ(si5).model)

    # Addition with overflowing cardinality
    si1 = SI(bits=8, stride=1, lower_bound=0, upper_bound=0xfe)
    si2 = SI(bits=8, stride=1, lower_bound=0xfe, upper_bound=0xff)
    nose.tools.assert_true((si1 + si2).model.is_top)

    # Addition that shouldn't get a TOP
    si1 = SI(bits=8, stride=1, lower_bound=0, upper_bound=0xfe)
    si2 = SI(bits=8, stride=1, lower_bound=0, upper_bound=0)
    nose.tools.assert_false((si1 + si2).model.is_top)

    # Subtraction
    si1 = SI(bits=8, stride=1, lower_bound=10, upper_bound=15)
    si2 = SI(bits=8, stride=1, lower_bound=11, upper_bound=12)
    si3 = SI(bits=8, stride=1, lower_bound=-2, upper_bound=4)
    nose.tools.assert_true((si1 - si2).ExactEQ(si3).model)

def test_vsa():
    from claripy.backends import BackendVSA
    from claripy.vsa import TrueResult, FalseResult, MaybeResult #pylint:disable=unused-variable

    clrp = claripy.Claripies["SerialZ3"]
    # Set backend
    b = BackendVSA()
    b.set_claripy_object(clrp)
    clrp.model_backends.append(b)
    clrp.solver_backends = []

    solver_type = claripy.solvers.BranchingSolver
    s = solver_type(clrp) #pylint:disable=unused-variable

    SI = clrp.StridedInterval
    VS = clrp.ValueSet
    BVV = clrp.BVV

    # Disable the use of DiscreteStridedIntervalSet
    claripy.vsa.strided_interval.allow_dsis = False

    def is_equal(ast_0, ast_1):
        return ast_0.ExactEQ(ast_1).model

    # Integers
    si1 = SI(bits=32, stride=0, lower_bound=10, upper_bound=10)
    si2 = SI(bits=32, stride=0, lower_bound=10, upper_bound=10)
    si3 = SI(bits=32, stride=0, lower_bound=28, upper_bound=28)
    # Strided intervals
    si_a = SI(bits=32, stride=2, lower_bound=10, upper_bound=20)
    si_b = SI(bits=32, stride=2, lower_bound=-100, upper_bound=200)
    si_c = SI(bits=32, stride=3, lower_bound=-100, upper_bound=200)
    si_d = SI(bits=32, stride=2, lower_bound=50, upper_bound=60)
    si_e = SI(bits=16, stride=1, lower_bound=0x2000, upper_bound=0x3000)
    si_f = SI(bits=16, stride=1, lower_bound=0, upper_bound=255)
    si_g = SI(bits=16, stride=1, lower_bound=0, upper_bound=0xff)
    si_h = SI(bits=32, stride=0, lower_bound=0x80000000, upper_bound=0x80000000)
    nose.tools.assert_true(is_equal(si1, 10))
    nose.tools.assert_true(is_equal(si2, 10))
    nose.tools.assert_true(is_equal(si1, si2))
    # __add__
    si_add_1 = si1 + si2
    nose.tools.assert_true(is_equal(si_add_1, SI(bits=32, stride=0, lower_bound=20, upper_bound=20)))
    si_add_2 = si1 + si_a
    nose.tools.assert_true(is_equal(si_add_2, SI(bits=32, stride=2, lower_bound=20, upper_bound=30)))
    si_add_3 = si_a + si_b
    nose.tools.assert_true(is_equal(si_add_3, SI(bits=32, stride=2, lower_bound=-90, upper_bound=220)))
    si_add_4 = si_b + si_c
    nose.tools.assert_true(is_equal(si_add_4, SI(bits=32, stride=1, lower_bound=-200, upper_bound=400)))
    # __add__ with overflow
    si_add_5 = si_h + 0xffffffff
    nose.tools.assert_true(is_equal(si_add_5, SI(bits=32, stride=0, lower_bound=0x7fffffff, upper_bound=0x7fffffff)))
    # __sub__
    si_minus_1 = si1 - si2
    nose.tools.assert_true(is_equal(si_minus_1, SI(bits=32, stride=0, lower_bound=0, upper_bound=0)))
    si_minus_2 = si_a - si_b
    nose.tools.assert_true(is_equal(si_minus_2, SI(bits=32, stride=2, lower_bound=-190, upper_bound=120)))
    si_minus_3 = si_b - si_c
    nose.tools.assert_true(is_equal(si_minus_3, SI(bits=32, stride=1, lower_bound=-300, upper_bound=300)))
    # __neg__ / __invert__
    si_neg_1 = ~si1
    nose.tools.assert_true(is_equal(si_neg_1, -11))
    si_neg_2 = ~si_b
    nose.tools.assert_true(is_equal(si_neg_2, SI(bits=32, stride=2, lower_bound=-201, upper_bound=99)))
    # __or__
    si_or_1 = si1 | si3
    nose.tools.assert_true(is_equal(si_or_1, 30))
    si_or_2 = si1 | si2
    nose.tools.assert_true(is_equal(si_or_2, 10))
    si_or_3 = si1 | si_a # An integer | a strided interval
    nose.tools.assert_true(is_equal(si_or_3 , SI(bits=32, stride=2, lower_bound=10, upper_bound=30)))
    si_or_3 = si_a | si1 # Exchange the operands
    nose.tools.assert_true(is_equal(si_or_3, SI(bits=32, stride=2, lower_bound=10, upper_bound=30)))
    si_or_4 = si_a | si_d # A strided interval | another strided interval
    nose.tools.assert_true(is_equal(si_or_4, SI(bits=32, stride=2, lower_bound=50, upper_bound=62)))
    si_or_4 = si_d | si_a # Exchange the operands
    nose.tools.assert_true(is_equal(si_or_4, SI(bits=32, stride=2, lower_bound=50, upper_bound=62)))
    si_or_5 = si_e | si_f #
    nose.tools.assert_true(is_equal(si_or_5, SI(bits=16, stride=1, lower_bound=0x2000, upper_bound=0x30ff)))
    si_or_6 = si_e | si_g #
    nose.tools.assert_true(is_equal(si_or_6, SI(bits=16, stride=1, lower_bound=0x2000, upper_bound=0x30ff)))
    # Shifting
    si_shl_1 = si1 << 3
    nose.tools.assert_equal(si_shl_1.size(), 32)
    nose.tools.assert_true(is_equal(si_shl_1, SI(bits=32, stride=0, lower_bound=80, upper_bound=80)))
    # Multiplication
    si_mul_1 = si1 * 3
    nose.tools.assert_equal(si_mul_1.size(), 32)
    nose.tools.assert_true(is_equal(si_mul_1, SI(bits=32, stride=0, lower_bound=30, upper_bound=30)))
    si_mul_2 = si_a * 3
    nose.tools.assert_equal(si_mul_2.size(), 32)
    nose.tools.assert_true(is_equal(si_mul_2, SI(bits=32, stride=6, lower_bound=30, upper_bound=60)))
    si_mul_3 = si_a * si_b
    nose.tools.assert_equal(si_mul_3.size(), 32)
    nose.tools.assert_true(is_equal(si_mul_3, SI(bits=32, stride=2, lower_bound=-2000, upper_bound=4000)))
    # Division
    si_div_1 = si1 / 3
    nose.tools.assert_equal(si_div_1.size(), 32)
    nose.tools.assert_true(is_equal(si_div_1, SI(bits=32, stride=0, lower_bound=3, upper_bound=3)))
    si_div_2 = si_a / 3
    nose.tools.assert_equal(si_div_2.size(), 32)
    nose.tools.assert_true(is_equal(si_div_2, SI(bits=32, stride=1, lower_bound=3, upper_bound=6)))
    # Modulo
    si_mo_1 = si1 % 3
    nose.tools.assert_equal(si_mo_1.size(), 32)
    nose.tools.assert_true(is_equal(si_mo_1, SI(bits=32, stride=0, lower_bound=1, upper_bound=1)))
    si_mo_2 = si_a % 3
    nose.tools.assert_equal(si_mo_2.size(), 32)
    nose.tools.assert_true(is_equal(si_mo_2, SI(bits=32, stride=1, lower_bound=0, upper_bound=2)))

    #
    # Extracting the sign bit
    #

    # a negative integer
    si = SI(bits=64, stride=0, lower_bound=-1, upper_bound=-1)
    sb = si[63: 63]
    nose.tools.assert_true(is_equal(sb, 1))

    # non-positive integers
    si = SI(bits=64, stride=1, lower_bound=-1, upper_bound=0)
    sb = si[63: 63]
    nose.tools.assert_true(is_equal(sb, SI(bits=1, stride=1, lower_bound=0, upper_bound=1)))

    # Extracting an integer
    si = SI(bits=64, stride=0, lower_bound=0x7fffffffffff0000, upper_bound=0x7fffffffffff0000)
    part1 = si[63 : 32]
    part2 = si[31 : 0]
    nose.tools.assert_true(is_equal(part1, SI(bits=32, stride=0, lower_bound=0x7fffffff, upper_bound=0x7fffffff)))
    nose.tools.assert_true(is_equal(part2, SI(bits=32, stride=0, lower_bound=0xffff0000, upper_bound=0xffff0000)))

    # Concatenating two integers
    si_concat = part1.concat(part2)
    nose.tools.assert_true(is_equal(si_concat, si.model))

    # Extracting a SI
    si = clrp.SI(bits=64, stride=0x9, lower_bound=0x1, upper_bound=0xa)
    part1 = si[63 : 32]
    part2 = si[31 : 0]
    nose.tools.assert_true(is_equal(part1, SI(bits=32, stride=0, lower_bound=0x0, upper_bound=0x0)))
    nose.tools.assert_true(is_equal(part2, SI(bits=32, stride=9, lower_bound=1, upper_bound=10)))

    # Concatenating two SIs
    si_concat = part1.concat(part2)
    nose.tools.assert_true(is_equal(si_concat, si))

    # Zero-Extend the low part
    si_zeroextended = part2.zero_extend(32)
    nose.tools.assert_true(is_equal(si_zeroextended, SI(bits=64, stride=9, lower_bound=1, upper_bound=10)))

    # Sign-extension
    si_signextended = part2.sign_extend(32)
    nose.tools.assert_true(is_equal(si_signextended, SI(bits=64, stride=9, lower_bound=1, upper_bound=10)))

    # Extract from the result above
    si_extracted = si_zeroextended.extract(31, 0)
    nose.tools.assert_true(is_equal(si_extracted, SI(bits=32, stride=9, lower_bound=1, upper_bound=10)))

    # Union
    si_union_1 = si1.union(si2)
    nose.tools.assert_true(is_equal(si_union_1. SI(bits=32, stride=0, lower_bound=10, upper_bound=10)))
    si_union_2 = si1.union(si3)
    nose.tools.assert_true(is_equal(si_union_2. SI(bits=32, stride=18, lower_bound=10, upper_bound=28)))
    si_union_3 = si1.union(si_a)
    nose.tools.assert_true(is_equal(si_union_3. SI(bits=32, stride=2, lower_bound=10, upper_bound=20)))
    si_union_4 = si_a.union(si_b)
    nose.tools.assert_true(is_equal(si_union_4. SI(bits=32, stride=2, lower_bound=-100, upper_bound=200)))
    si_union_5 = si_b.union(si_c)
    nose.tools.assert_true(is_equal(si_union_5. SI(bits=32, stride=1, lower_bound=-100, upper_bound=200)))

    # Intersection
    si_intersection_1 = si1.intersection(si1)
    nose.tools.assert_true(is_equal(si_intersection_1, si2))
    si_intersection_2 = si1.intersection(si2)
    nose.tools.assert_true(is_equal(si_intersection_2, SI(bits=32, stride=0, lower_bound=10, upper_bound=10)))
    si_intersection_3 = si1.intersection(si_a)
    nose.tools.assert_true(is_equal(si_intersection_3, SI(bits=32, stride=0, lower_bound=10, upper_bound=10)))
    si_intersection_4 = si_a.intersection(si_b)
    nose.tools.assert_true(is_equal(si_intersection_4, SI(bits=32, stride=2, lower_bound=10, upper_bound=20)))
    si_intersection_5 = si_b.intersection(si_c)
    nose.tools.assert_true(is_equal(si_intersection_5, SI(bits=32, stride=6, lower_bound=-100, upper_bound=200)))

    # Sign-extension
    si = SI(bits=1, stride=0, lower_bound=1, upper_bound=1)
    si_signextended = si.sign_extend(31)
    nose.tools.assert_true(is_equal(si_signextended.model. SI(bits=32, stride=0, lower_bound=0xffffffff, upper_bound=0xffffffff)))

    # Comparison between SI and BVV
    si = SI(bits=32, stride=1, lower_bound=-0x7f, upper_bound=0x7f)
    si.uninitialized = True
    bvv = BVV(0x30, 32)
    comp = (si < bvv)
    nose.tools.assert_equal(comp.model, MaybeResult())

    # Better extraction
    # si = <32>0x1000000[0xcffffff, 0xdffffff]R
    si = SI(bits=32, stride=0x1000000, lower_bound=0xcffffff, upper_bound=0xdffffff)
    si_byte0 = si[7: 0]
    si_byte1 = si[15: 8]
    si_byte2 = si[23: 16]
    si_byte3 = si[31: 24]
    nose.tools.assert_true(is_equal(si_byte0, SI(bits=8, stride=0, lower_bound=0xff, upper_bound=0xff)))
    nose.tools.assert_true(is_equal(si_byte1, SI(bits=8, stride=0, lower_bound=0xff, upper_bound=0xff)))
    nose.tools.assert_true(is_equal(si_byte2, SI(bits=8, stride=0, lower_bound=0xff, upper_bound=0xff)))
    nose.tools.assert_true(is_equal(si_byte3, SI(bits=8, stride=1, lower_bound=0xc, upper_bound=0xd)))

    # Optimization on bitwise-and
    si_1 = SI(bits=32, stride=1, lower_bound=0x0, upper_bound=0xffffffff)
    si_2 = SI(bits=32, stride=0, lower_bound=0x80000000, upper_bound=0x80000000)
    si = si_1 & si_2
    nose.tools.assert_true(is_equal(si, SI(bits=32, stride=0x80000000, lower_bound=0, upper_bound=0x80000000)))

    si_1 = SI(bits=32, stride=1, lower_bound=0x0, upper_bound=0x7fffffff)
    si_2 = SI(bits=32, stride=0, lower_bound=0x80000000, upper_bound=0x80000000)
    si = si_1 & si_2
    nose.tools.assert_true(is_equal(si, SI(bits=32, stride=0, lower_bound=0, upper_bound=0)))

    #
    # ValueSet
    #

    vs_1 = clrp.ValueSet(bits=32)
    nose.tools.assert_true(vs_1.model.is_empty(), True)
    # Test merging two addresses
    vs_1.model.merge_si('global', si1)
    vs_1.model.merge_si('global', si3)
    nose.tools.assert_true(is_equal(vs_1.model.get_si('global'), SI(bits=32, stride=18, lower_bound=10, upper_bound=28)))
    # Length of this ValueSet
    nose.tools.assert_equal(len(vs_1.model), 32)

    #
    # IfProxy
    #

    # max and min on IfProxy
    si = SI(bits=32, stride=1, lower_bound=0, upper_bound=0xffffffff)
    if_0 = clrp.If(si == 0, si, si - 1)
    max_val = b.max(if_0)
    min_val = b.min(if_0)
    nose.tools.assert_true(max_val, 0xffffffff)
    nose.tools.assert_true(min_val, -0x80000000)

    # if_1 = And(VS_2, IfProxy(si == 0, 0, 1))
    vs_2 = VS(region='global', bits=32, val=0xFA7B00B)
    si = SI(bits=32, stride=1, lower_bound=0, upper_bound=1)
    if_1 = (vs_2 & clrp.If(si == 0, SI(bits=32, stride=0, lower_bound=0, upper_bound=0), SI(bits=32, stride=0, lower_bound=0xffffffff, upper_bound=0xffffffff)))
    nose.tools.assert_true(is_equal(if_1.model.trueexpr, VS(region='global', bits=32, val=0)))
    nose.tools.assert_true(is_equal(if_1.model.falseexpr, vs_2))

    # if_2 = And(VS_3, IfProxy(si != 0, 0, 1)
    vs_3 = clrp.ValueSet(region='global', bits=32, val=0xDEADCA7)
    si = clrp.SI(bits=32, stride=1, lower_bound=0, upper_bound=1)
    if_2 = (vs_3 & clrp.If(si != 0, SI(bits=32, stride=0, lower_bound=0, upper_bound=0), SI(bits=32, stride=0, lower_bound=0xffffffff, upper_bound=0xffffffff)))
    nose.tools.assert_true(is_equal(if_2.model.trueexpr, VS(region='global', bits=32, val=0)))
    nose.tools.assert_true(is_equal(if_2.model.falseexpr, vs_3))

    # Something crazy is gonna happen...
    if_3 = if_1 + if_2
    nose.tools.assert_true(is_equal(if_3.model.trueexpr, vs_3))
    nose.tools.assert_true(is_equal(if_3.model.falseexpr, vs_2))

def test_vsa_constraint_to_si():
    from claripy.backends import BackendVSA
    from claripy.vsa import TrueResult, FalseResult, MaybeResult  # pylint:disable=unused-variable

    clrp = claripy.Claripies["SerialZ3"]
    # Set backend
    b = BackendVSA()
    b.set_claripy_object(clrp)
    clrp.model_backends.append(b)
    clrp.solver_backends = [ ]

    solver_type = claripy.solvers.BranchingSolver
    s = solver_type(clrp)  #pylint:disable=unused-variable

    SI = clrp.SI
    BVV = clrp.BVV

    claripy.vsa.strided_interval.allow_dsis = False

    #
    # If(SI == 0, 1, 0) == 1
    #

    s1 = SI(bits=32, stride=1, lower_bound=0, upper_bound=2)
    ast_true = (clrp.If(s1 == BVV(0, 32), BVV(1, 1), BVV(0, 1)) == BVV(1, 1))
    ast_false = (clrp.If(s1 == BVV(0, 32), BVV(1, 1), BVV(0, 1)) != BVV(1, 1))

    trueside_sat, trueside_replacement = b.constraint_to_si(ast_true)
    nose.tools.assert_equal(trueside_sat, True)
    nose.tools.assert_equal(len(trueside_replacement), 1)
    nose.tools.assert_true(trueside_replacement[0][0] is s1)
    # True side: SI<32>0[0, 0]
    nose.tools.assert_true(
        clrp.is_true(trueside_replacement[0][1] == SI(bits=32, stride=0, lower_bound=0, upper_bound=0)))

    falseside_sat, falseside_replacement = b.constraint_to_si(ast_false)
    nose.tools.assert_equal(falseside_sat, True)
    nose.tools.assert_equal(len(falseside_replacement), 1)
    nose.tools.assert_true(falseside_replacement[0][0] is s1)
    # False side; SI<32>1[1, 2]
    nose.tools.assert_true(
        clrp.is_true(falseside_replacement[0][1] == SI(bits=32, stride=1, lower_bound=1, upper_bound=2)))

    #
    # Extract(0, 0, Concat(BVV(0, 63), If(SI == 0, 1, 0))) == 1
    #

    s2 = SI(bits=32, stride=1, lower_bound=0, upper_bound=2)
    ast_true = (clrp.Extract(0, 0, clrp.Concat(BVV(0, 63), clrp.If(s2 == 0, BVV(1, 1), BVV(0, 1)))) == 1)
    ast_false = (clrp.Extract(0, 0, clrp.Concat(BVV(0, 63), clrp.If(s2 == 0, BVV(1, 1), BVV(0, 1)))) != 1)

    trueside_sat, trueside_replacement = b.constraint_to_si(ast_true)
    nose.tools.assert_equal(trueside_sat, True)
    nose.tools.assert_equal(len(trueside_replacement), 1)
    nose.tools.assert_true(trueside_replacement[0][0] is s2)
    # True side: SI<32>0[0, 0]
    nose.tools.assert_true(
        clrp.is_true(trueside_replacement[0][1] == SI(bits=32, stride=0, lower_bound=0, upper_bound=0)))

    falseside_sat, falseside_replacement = b.constraint_to_si(ast_false)
    nose.tools.assert_equal(falseside_sat, True)
    nose.tools.assert_equal(len(falseside_replacement), 1)
    nose.tools.assert_true(falseside_replacement[0][0] is s2)
    # False side; SI<32>1[1, 2]
    nose.tools.assert_true(
        clrp.is_true(falseside_replacement[0][1] == SI(bits=32, stride=1, lower_bound=1, upper_bound=2)))

    #
    # Extract(0, 0, ZeroExt(32, If(SI == 0, BVV(1, 32), BVV(0, 32)))) == 1
    #

    s3 = SI(bits=32, stride=1, lower_bound=0, upper_bound=2)
    ast_true = (clrp.Extract(0, 0, clrp.ZeroExt(32, clrp.If(s3 == 0, BVV(1, 32), BVV(0, 32)))) == 1)
    ast_false = (clrp.Extract(0, 0, clrp.ZeroExt(32, clrp.If(s3 == 0, BVV(1, 32), BVV(0, 32)))) != 1)

    trueside_sat, trueside_replacement = b.constraint_to_si(ast_true)
    nose.tools.assert_equal(trueside_sat, True)
    nose.tools.assert_equal(len(trueside_replacement), 1)
    nose.tools.assert_true(trueside_replacement[0][0] is s3)
    # True side: SI<32>0[0, 0]
    nose.tools.assert_true(
        clrp.is_true(trueside_replacement[0][1] == SI(bits=32, stride=0, lower_bound=0, upper_bound=0)))

    falseside_sat, falseside_replacement = b.constraint_to_si(ast_false)
    nose.tools.assert_equal(falseside_sat, True)
    nose.tools.assert_equal(len(falseside_replacement), 1)
    nose.tools.assert_true(falseside_replacement[0][0] is s3)
    # False side; SI<32>1[1, 2]
    nose.tools.assert_true(
        clrp.is_true(falseside_replacement[0][1] == SI(bits=32, stride=1, lower_bound=1, upper_bound=2)))

    #
    # Extract(0, 0, ZeroExt(32, If(Extract(32, 0, (SI & SI)) < 0, BVV(1, 1), BVV(0, 1))))
    #

    s4 = SI(bits=64, stride=1, lower_bound=0, upper_bound=0xffffffffffffffff)
    ast_true = (
        clrp.Extract(0, 0, clrp.ZeroExt(32, clrp.If(clrp.Extract(31, 0, (s4 & s4)) < 0, BVV(1, 32), BVV(0, 32)))) == 1)
    ast_false = (
        clrp.Extract(0, 0, clrp.ZeroExt(32, clrp.If(clrp.Extract(31, 0, (s4 & s4)) < 0, BVV(1, 32), BVV(0, 32)))) != 1)

    trueside_sat, trueside_replacement = b.constraint_to_si(ast_true)
    nose.tools.assert_equal(trueside_sat, True)
    nose.tools.assert_equal(len(trueside_replacement), 1)
    nose.tools.assert_true(trueside_replacement[0][0] is s4)
    # True side: SI<32>0[0, 0]
    nose.tools.assert_true(
        clrp.is_true(trueside_replacement[0][1] == SI(bits=64, stride=1, lower_bound=-0x8000000000000000, upper_bound=-1)))

    falseside_sat, falseside_replacement = b.constraint_to_si(ast_false)
    nose.tools.assert_equal(falseside_sat, True)
    nose.tools.assert_equal(len(falseside_replacement), 1)
    nose.tools.assert_true(falseside_replacement[0][0] is s4)
    # False side; SI<32>1[1, 2]
    nose.tools.assert_true(
        clrp.is_true(falseside_replacement[0][1] == SI(bits=64, stride=1, lower_bound=0, upper_bound=0x7fffffffffffffff)))

    # TODO: Add some more insane test cases

def test_vsa_discrete_value_set():
    """
    Test cases for DiscreteStridedIntervalSet.
    """
    from claripy.backends import BackendVSA
    from claripy.vsa import BoolResult, StridedInterval, DiscreteStridedIntervalSet #pylint:disable=unused-variable

    clrp = claripy.Claripies["SerialZ3"]
    # Set backend
    b = BackendVSA()
    b.set_claripy_object(clrp)
    clrp.model_backends.append(b)
    clrp.solver_backends = []

    solver_type = claripy.solvers.BranchingSolver
    s = solver_type(clrp) #pylint:disable=unused-variable

    SI = clrp.StridedInterval
    VS = clrp.ValueSet
    BVV = clrp.BVV

    # Allow the use of DiscreteStridedIntervalSet (cuz we wanna test it!)
    claripy.vsa.strided_interval.allow_dsis = True

    #
    # Union
    #
    val_1 = BVV(0, 32)
    val_2 = BVV(1, 32)
    r = val_1.union(val_2)
    nose.tools.assert_true(isinstance(r.model, DiscreteStridedIntervalSet))
    nose.tools.assert_true(r.model.collapse(), SI(bits=32, stride=1, lower_bound=0, upper_bound=1))

    r = r.union(BVV(3, 32))
    ints = b.eval(r, 4)
    nose.tools.assert_equal(len(ints), 3)
    nose.tools.assert_equal(ints, [0, 1, 3])

    #
    # Intersection
    #

    val_1 = BVV(0, 32)
    val_2 = BVV(1, 32)
    r = val_1.intersection(val_2)
    nose.tools.assert_true(isinstance(r.model, StridedInterval))
    nose.tools.assert_true(r.model.is_empty())

    val_1 = SI(bits=32, stride=1, lower_bound=0, upper_bound=10)
    val_2 = SI(bits=32, stride=1, lower_bound=10, upper_bound=20)
    val_3 = SI(bits=32, stride=1, lower_bound=15, upper_bound=50)
    r = val_1.union(val_2)
    nose.tools.assert_true(isinstance(r.model, DiscreteStridedIntervalSet))
    r = r.intersection(val_3)
    nose.tools.assert_equal(sorted(b.eval(r, 100)), [ 15, 16, 17, 18, 19, 20 ])

    #
    # Some logical operations
    #

    val_1 = SI(bits=32, stride=1, lower_bound=0, upper_bound=10)
    val_2 = SI(bits=32, stride=1, lower_bound=5, upper_bound=20)
    r_1 = val_1.union(val_2)
    val_3 = SI(bits=32, stride=1, lower_bound=20, upper_bound=30)
    val_4 = SI(bits=32, stride=1, lower_bound=25, upper_bound=35)
    r_2 = val_3.union(val_4)
    nose.tools.assert_true(isinstance(r_1.model, DiscreteStridedIntervalSet))
    nose.tools.assert_true(isinstance(r_2.model, DiscreteStridedIntervalSet))
    # r_1 < r_2
    nose.tools.assert_true(BoolResult.is_maybe(r_1 < r_2))
    # r_1 <= r_2
    nose.tools.assert_true(BoolResult.is_true(r_1 <= r_2))
    # r_1 >= r_2
    nose.tools.assert_true(BoolResult.is_maybe(r_1 >= r_2))
    # r_1 > r_2
    nose.tools.assert_true(BoolResult.is_false(r_1 > r_2))
    # r_1 == r_2
    nose.tools.assert_true(BoolResult.is_maybe(r_1 == r_2))
    # r_1 != r_2
    nose.tools.assert_true(BoolResult.is_maybe(r_1 != r_2))

    #
    # Some arithmetic operations
    #

    val_1 = SI(bits=32, stride=1, lower_bound=0, upper_bound=10)
    val_2 = SI(bits=32, stride=1, lower_bound=5, upper_bound=20)
    r_1 = val_1.union(val_2)
    val_3 = SI(bits=32, stride=1, lower_bound=20, upper_bound=30)
    val_4 = SI(bits=32, stride=1, lower_bound=25, upper_bound=35)
    r_2 = val_3.union(val_4)
    nose.tools.assert_true(isinstance(r_1.model, DiscreteStridedIntervalSet))
    nose.tools.assert_true(isinstance(r_2.model, DiscreteStridedIntervalSet))
    # r_1 + r_2
    r = r_1 + r_2
    nose.tools.assert_true(isinstance(r.model, DiscreteStridedIntervalSet))
    nose.tools.assert_true(BoolResult.is_true(r == SI(bits=32, stride=1, lower_bound=20, upper_bound=55)))
    # r_2 - r_1
    r = r_2 - r_1
    nose.tools.assert_true(isinstance(r.model, DiscreteStridedIntervalSet))
    nose.tools.assert_true(BoolResult.is_true(r == SI(bits=32, stride=1, lower_bound=0, upper_bound=35)))

def test_simplification():
    clrp = claripy.Claripies['SerialZ3']

    def assert_identical(a, b):
        nose.tools.assert_true(a.identical(b))

    x, y, z = (clrp.BV(name, 32) for name in ('x', 'y', 'z'))

    # test extraction of concatted values
    concatted = clrp.Concat(x, y, z)

    assert_identical(concatted[95:64].reduced, x)
    assert_identical(concatted[63:32].reduced, y)
    assert_identical(concatted[31:0].reduced, z)

    assert_identical(concatted[95:32].reduced, clrp.Concat(x, y))
    assert_identical(concatted[63:0].reduced, clrp.Concat(y, z))

    assert_identical(concatted[95:0].reduced, concatted)

    assert_identical(concatted[47:0].reduced, clrp.Concat(y, z)[47:0])
    assert_identical(concatted[70:0].reduced, concatted[70:0])
    assert_identical(concatted[70:15].reduced, concatted[70:15])
    assert_identical(concatted[70:35].reduced, clrp.Concat(x, y)[38:3])

    # TODO: add more tests

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
        test_vsa()
        test_vsa_constraint_to_si()
        test_vsa_discrete_value_set()
        test_simplification()
    print "WOO"

    print 'eval', claripy.solvers.solver.cached_evals
    print 'min', claripy.solvers.solver.cached_min
    print 'max', claripy.solvers.solver.cached_max
    print 'solve', claripy.solvers.solver.cached_solve
