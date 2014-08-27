import nose
import logging
l = logging.getLogger("claripy.test")

import pickle
import tempfile
import claripy

import logging
l = logging.getLogger("claripy.test")

def test_expression():
	clrp = claripy.ClaripyStandalone()

	e = clrp.BitVecVal(0x01020304, 32)
	nose.tools.assert_equal(len(e), 32)
	r = e.reversed()
	nose.tools.assert_equal(r.eval(), 0x04030201)
	nose.tools.assert_equal(len(r), 32)

	nose.tools.assert_equal([ i.eval() for i in r.chop(8) ], [ 4, 3, 2, 1 ] )

	e1 = r[31:24]
	nose.tools.assert_equal(e1.eval(), 0x04)
	nose.tools.assert_equal(len(e1), 8)
	nose.tools.assert_equal(e1[2].eval(), 1)
	nose.tools.assert_equal(e1[1].eval(), 0)

	ee1 = e1.zero_extend(8)
	nose.tools.assert_equal(ee1.eval(), 0x0004)
	nose.tools.assert_equal(len(ee1), 16)

	ee1 = clrp.BitVecVal(0xfe, 8).sign_extend(8)
	nose.tools.assert_equal(ee1.eval(), 0xfffe)
	nose.tools.assert_equal(len(ee1), 16)

	xe1 = [ i.eval() for i in e1.chop(1) ]
	nose.tools.assert_equal(xe1, [ 0, 0, 0, 0, 0, 1, 0, 0 ])

def test_actualization():
	clrp = claripy.ClaripyStandalone()

	ba = claripy.backends.BackendAbstract(clrp)
	bc = claripy.backends.BackendConcrete(clrp)
	clrp.expression_backends = [ ba, bc ]

	a = claripy.E(clrp, obj=5, variables=set(), symbolic=False)
	b = a+a
	nose.tools.assert_is(b._obj, None)
	nose.tools.assert_is(type(b._ast), claripy.A)

	b.eval(backends=[bc], save=True)
	nose.tools.assert_equal(b._obj, 10)

def test_fallback_abstraction():
	clrp = claripy.ClaripyStandalone()
	ba = claripy.backends.BackendAbstract(clrp)
	bc = claripy.backends.BackendConcrete(clrp)
	bz = claripy.backends.BackendZ3(clrp)
	clrp.expression_backends = [ bc, ba ]

	a = claripy.E(clrp, obj=5, variables=set(), symbolic=False)
	b = claripy.E(clrp, ast=claripy.A(op='BitVec', args=('x', 32)), variables={'x'}, symbolic=True)
	c = a+b
	d = 5+b
	e = b+5
	f = b+b

	nose.tools.assert_false(a.symbolic)
	nose.tools.assert_true(b.symbolic)
	nose.tools.assert_true(c.symbolic)
	nose.tools.assert_true(d.symbolic)
	nose.tools.assert_true(e.symbolic)
	nose.tools.assert_true(f.symbolic)

	a.eval(backends=[bc, bz], save=True)
	nose.tools.assert_equal(str(a._obj), '5')
	nose.tools.assert_is(type(a._obj), int)

	b.eval(backends=[bc, bz], save=True)
	nose.tools.assert_equal(str(b._obj), 'x')
	nose.tools.assert_equal(b._obj.__module__, 'z3')

	c.eval(backends=[bc, bz], save=True)
	d.eval(backends=[bc, bz], save=True)
	e.eval(backends=[bc, bz], save=True)
	f.eval(backends=[bc, bz], save=True)

	nose.tools.assert_equal(str(c._obj), '5 + x')
	nose.tools.assert_equal(str(d._obj), '5 + x')
	nose.tools.assert_equal(str(e._obj), 'x + 5')
	nose.tools.assert_equal(str(f._obj), 'x + x')

	f._ast = None
	f.abstract([bc, bz])
	f._obj = None
	f.eval(backends=[bc, bz], save=True)
	nose.tools.assert_equal(str(f._obj), 'x + x')

def test_mixed_z3():
	clrp = claripy.ClaripyStandalone()
	ba = claripy.backends.BackendAbstract(clrp)
	bc = claripy.backends.BackendConcrete(clrp)
	bz = claripy.backends.BackendZ3(clrp)

	clrp.expression_backends = [ bc, bz, ba ]
	a = claripy.E(clrp, ast=claripy.A(op='BitVecVal', args=(0, 32)), variables=set(), symbolic=False)
	b = claripy.E(clrp, ast=claripy.A(op='BitVec', args=('x', 32)), variables={'x'}, symbolic=True)
	nose.tools.assert_true(b.symbolic)
	c = a+b
	nose.tools.assert_true(b.symbolic)
	nose.tools.assert_true(c.symbolic)

	a.eval()
	b.eval()

	nose.tools.assert_is(type(a._obj), claripy.bv.BVV)
	nose.tools.assert_equal(b._obj.__module__, 'z3')

	d = a + b
	nose.tools.assert_equal(d._obj.__module__, 'z3')
	nose.tools.assert_equal(str(d._obj), '0 + x')

	c.eval()
	nose.tools.assert_equal(c._obj.__module__, 'z3')
	nose.tools.assert_equal(str(c._obj), '0 + x')

def test_pickle():
	clrp = claripy.ClaripyStandalone()
	ba = claripy.backends.BackendAbstract(clrp)
	bc = claripy.backends.BackendConcrete(clrp)
	bz = claripy.backends.BackendZ3(clrp)
	clrp.expression_backends = [ bc, bz, ba ]

	a = claripy.E(clrp, ast=claripy.A(op='BitVecVal', args=(0, 32)), variables=set(), symbolic=False)
	b = claripy.E(clrp, ast=claripy.A(op='BitVec', args=('x', 32)), variables={'x'}, symbolic=True)
	a.eval(); a._ast = None
	b.eval(); a._ast = None

	c = a+b
	nose.tools.assert_equal(c._obj.__module__, 'z3')
	nose.tools.assert_equal(str(c._obj), '0 + x')

	c_copy = pickle.loads(pickle.dumps(c))
	nose.tools.assert_is(c_copy._obj, None)
	c_copy._claripy = clrp
	c_copy.eval()
	nose.tools.assert_equal(c_copy._obj.__module__, 'z3')
	nose.tools.assert_equal(str(c_copy._obj), '0 + x')

def test_datalayer():
	l.info("Running test_datalayer")

	clrp = claripy.ClaripyStandalone()
	pickle_dir = tempfile.mkdtemp()
	clrp.dl = claripy.DataLayer(pickle_dir=pickle_dir)
	l.debug("Pickling to %s",pickle_dir)

	ba = claripy.backends.BackendAbstract(claripy.claripy)
	bc = claripy.backends.BackendConcrete(claripy.claripy)
	bz = claripy.backends.BackendZ3(claripy.claripy)
	clrp.expression_backends = [ bc, ba ]

	a = claripy.E(clrp, ast=claripy.A(op='BitVecVal', args=(0, 32)), variables=set(), symbolic=False)
	b = claripy.E(clrp, ast=claripy.A(op='BitVec', args=('x', 32)), variables={'x'}, symbolic=True)

	a.eval(); a._ast = None
	b.store()
	#b.eval(); b._ast = None
	c = a + b
	c.store()

	c.eval(backends=[ bc, bz ], save=True)
	nose.tools.assert_equal(str(c._obj), '0 + x')

	d = a+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b
	d.store()

	l.debug("Loading stage!")
	clrp.dl = claripy.DataLayer(pickle_dir=pickle_dir)
	nose.tools.assert_equal(len(clrp.dl._cache), 0)

	e = clrp.dl.load_expression(c._uuid)
	e.eval([ bc, bz ], save=True)
	nose.tools.assert_equal(str(e._obj), '0 + x')

def test_model():
	clrp = claripy.ClaripyStandalone()
	bc = claripy.backends.BackendConcrete(clrp)
	ba = claripy.backends.BackendAbstract(clrp)
	clrp.expression_backends = [ bc, ba ]

	a = claripy.E(clrp, ast=claripy.A(op='BitVecVal', args=(5, 32)), variables=set(), symbolic=False)
	b = claripy.E(clrp, ast=claripy.A(op='BitVec', args=('x', 32)), variables={'x'}, symbolic=True)

	c = a + b

	r_c = c.eval(backends=[bc], save=False, model={'x': 10})
	nose.tools.assert_equal(r_c, 15)
	r_d = c.eval(backends=[bc], model={'x': 15}, save=False)
	nose.tools.assert_equal(r_c, 15)
	nose.tools.assert_equal(r_d, 20)

def test_solver():
	raw_solver(claripy.solvers.BranchingSolver)
	raw_solver(claripy.solvers.CompositeSolver)
def raw_solver(solver_type):
	clrp = claripy.ClaripyStandalone()
	#bc = claripy.backends.BackendConcrete(clrp)
	#bz = claripy.backends.BackendZ3(clrp)
	#ba = claripy.backends.BackendAbstract(clrp)
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
	nose.tools.assert_equal(s.eval_value(x + 5, 1)[0], 15)
	nose.tools.assert_true(s.solution(x + 5, 15))
	nose.tools.assert_true(s.solution(x, 10))
	nose.tools.assert_true(s.solution(y, 15))
	nose.tools.assert_false(s.solution(y, 13))


	shards = s.split()
	nose.tools.assert_equal(len(shards), 2)
	nose.tools.assert_equal(len(shards[0].variables), 1)
	nose.tools.assert_equal(len(shards[1].variables), 1)
	nose.tools.assert_equal({ len(shards[0].constraints), len(shards[1].constraints) }, { 1, 2 }) # adds the != from the solution() check

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

	nose.tools.assert_equal(s.max_value(z), 4)
	nose.tools.assert_equal(s.min_value(z), 0)
	nose.tools.assert_equal(s.min_value(y), 22)
	nose.tools.assert_equal(s.max_value(y), 2**y.size()-1)

	ss = s.split()
	nose.tools.assert_equal(len(ss), 2)
	if type(s) is claripy.solvers.BranchingSolver:
		nose.tools.assert_equal({ len(_.constraints) for _ in ss }, { 2, 3 }) # constraints from min or max
	elif type(s) is claripy.solvers.CompositeSolver:
		nose.tools.assert_equal({ len(_.constraints) for _ in ss }, { 2, 2 }) # constraints from min or max

	# test that False makes it unsat
	s = solver_type(clrp)
	s.add(clrp.BitVecVal(1,1) == clrp.BitVecVal(1,1))
	nose.tools.assert_true(s.satisfiable())
	s.add(clrp.BitVecVal(1,1) == clrp.BitVecVal(0,1))
	nose.tools.assert_false(s.satisfiable())

	# test extra constraints
	s = solver_type(clrp)
	x = clrp.BitVec('x', 32)
	nose.tools.assert_equal(s.eval_value(x, 2, extra_constraints=[x==10]), [ 10 ])
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
	clrp = claripy.ClaripyStandalone()
	s = solver_type(clrp)
	x = clrp.BitVec("x", 32)
	y = clrp.BitVec("y", 32)
	s.add(x > y)
	s.add(x < 10)

	t = s.branch()
	if type(s) is claripy.solvers.BranchingSolver:
		nose.tools.assert_is(s._solver, t._solver)
		nose.tools.assert_true(s._finalized)
		nose.tools.assert_true(t._finalized)
	t.add(x > 5)
	if type(s) is claripy.solvers.BranchingSolver:
		nose.tools.assert_false(s._solver is t._solver)

	s.add(x == 3)
	nose.tools.assert_true(s.satisfiable())
	t.add(x == 3)
	nose.tools.assert_false(t.satisfiable())

	s.add(y == 2)
	nose.tools.assert_true(s.satisfiable())
	nose.tools.assert_equals(s.eval_value(x, 1)[0], 3)
	nose.tools.assert_equals(s.eval_value(y, 1)[0], 2)
	nose.tools.assert_false(t.satisfiable())

def test_combine():
	raw_combine(claripy.solvers.BranchingSolver)
	raw_combine(claripy.solvers.CompositeSolver)
def raw_combine(solver_type):
	clrp = claripy.ClaripyStandalone()
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
	nose.tools.assert_equal(s30.combine([s10]).eval_value(x, 1), [ 30 ])
	nose.tools.assert_equal(len(s30.combine([s10]).constraints), 2)

def test_bv():
	claripy.bv.test()

def test_simple_merging():
	raw_simple_merging(claripy.solvers.BranchingSolver)
	raw_simple_merging(claripy.solvers.CompositeSolver)
def raw_simple_merging(solver_type):
	clrp = claripy.ClaripyStandalone()
	s1 = solver_type(clrp)
	s2 = solver_type(clrp)
	w = clrp.BitVec("w", 8)
	x = clrp.BitVec("x", 8)
	y = clrp.BitVec("y", 8)
	z = clrp.BitVec("z", 8)
	m = clrp.BitVec("m", 8)

	s1.add(x == 1, y == 10)
	s2.add(x == 2, z == 20, w == 5)
	sm = s1.merge([s2], m, [ 0, 1 ])

	nose.tools.assert_equal(s1.eval_value(x, 1), [1])
	nose.tools.assert_equal(s2.eval_value(x, 1), [2])

	sm1 = sm.branch()
	sm1.add(x == 1)
	nose.tools.assert_equal(sm1.eval_value(x, 1), [1])
	nose.tools.assert_equal(sm1.eval_value(y, 1), [10])
	nose.tools.assert_equal(sm1.eval_value(z, 1), [0])
	nose.tools.assert_equal(sm1.eval_value(w, 1), [0])

	sm2 = sm.branch()
	sm2.add(x == 2)
	nose.tools.assert_equal(sm2.eval_value(x, 1), [2])
	nose.tools.assert_equal(sm2.eval_value(y, 1), [0])
	nose.tools.assert_equal(sm2.eval_value(z, 1), [20])
	nose.tools.assert_equal(sm2.eval_value(w, 1), [5])

	sm1 = sm.branch()
	sm1.add(m == 0)
	nose.tools.assert_equal(sm1.eval_value(x, 1), [1])
	nose.tools.assert_equal(sm1.eval_value(y, 1), [10])
	nose.tools.assert_equal(sm1.eval_value(z, 1), [0])
	nose.tools.assert_equal(sm1.eval_value(w, 1), [0])

	sm2 = sm.branch()
	sm2.add(m == 1)
	nose.tools.assert_equal(sm2.eval_value(x, 1), [2])
	nose.tools.assert_equal(sm2.eval_value(y, 1), [0])
	nose.tools.assert_equal(sm2.eval_value(z, 1), [20])
	nose.tools.assert_equal(sm2.eval_value(w, 1), [5])

	m2 = clrp.BitVec("m2", 32)
	smm = sm1.merge([sm2], m2, [0, 1])

	smm_1 = smm.branch()
	smm_1.add(x == 1)
	nose.tools.assert_equal(smm_1.eval_value(x, 1), [1])
	nose.tools.assert_equal(smm_1.eval_value(y, 1), [10])
	nose.tools.assert_equal(smm_1.eval_value(z, 1), [0])
	nose.tools.assert_equal(smm_1.eval_value(w, 1), [0])

	smm_2 = smm.branch()
	smm_2.add(m == 1)
	nose.tools.assert_equal(smm_2.eval_value(x, 1), [2])
	nose.tools.assert_equal(smm_2.eval_value(y, 1), [0])
	nose.tools.assert_equal(smm_2.eval_value(z, 1), [20])
	nose.tools.assert_equal(smm_2.eval_value(w, 1), [5])

	so = solver_type(clrp)
	so.add(w == 0)

	sa = so.branch()
	sb = so.branch()
	sa.add(x == 1)
	sb.add(x == 2)
	sm = sa.merge([sb], m, [0, 1])

	smc = sm.branch()
	smd = sm.branch()
	smc.add(y == 3)
	smd.add(y == 4)

	smm = smc.merge([smd], m2, [0, 1])
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
	clrp = claripy.ClaripyStandalone()
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
	clrp = claripy.ClaripyStandalone()
	s = solver_type(clrp)
	x = clrp.BitVec("x", 32)
	y = clrp.BitVec("y", 32)
	z = clrp.BitVec("z", 32)

	ite = clrp.ite_dict(x, {1:11, 2:22, 3:33, 4:44, 5:55, 6:66, 7:77, 8:88, 9:99}, clrp.BitVecVal(0, 32))
	nose.tools.assert_equal(sorted(s.eval_value(ite, 100)), [ 0, 11, 22, 33, 44, 55, 66, 77, 88, 99 ] )

	ss = s.branch()
	ss.add(ite == 88)
	nose.tools.assert_equal(sorted(ss.eval_value(ite, 100)), [ 88 ] )
	nose.tools.assert_equal(sorted(ss.eval_value(x, 100)), [ 8 ] )

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
	nose.tools.assert_equal(sorted(ss.eval_value(ity, 100)), [ 99, 123 ] )
	nose.tools.assert_equal(sorted(ss.eval_value(x, 100)), [ 3, 9 ] )
	nose.tools.assert_equal(sorted(ss.eval_value(y, 100)), [ 123 ] )

	itz = clrp.ite_cases([ (clrp.And(x == 10, y == 20), 33), (clrp.And(x==1, y==2), 3), (clrp.And(x==100, y==200), 333) ], clrp.BitVecVal(0, 32))
	ss = s.branch()
	ss.add(z == itz)
	ss.add(itz != 0)
	nose.tools.assert_equal(ss.eval_value(y/x, 100), [ 2 ])
	nose.tools.assert_equal(sorted(ss.eval_value(x, 100)), [ 1, 10, 100 ])
	nose.tools.assert_equal(sorted(ss.eval_value(y, 100)), [ 2, 20, 200 ])

def test_bool():
	clrp = claripy.ClaripyStandalone()

	a = clrp.And(*[False, False, True])
	nose.tools.assert_equal(a.eval(), False)
	a = clrp.And(*[True, True, True])
	nose.tools.assert_equal(a.eval(), True)

	o = clrp.Or(*[False, False, True])
	nose.tools.assert_equal(o.eval(), True)
	o = clrp.Or(*[False, False, False])
	nose.tools.assert_equal(o.eval(), False)

if __name__ == '__main__':
	logging.getLogger('claripy.test').setLevel(logging.DEBUG)
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

	test_expression()
	test_actualization()
	test_fallback_abstraction()
	test_mixed_z3()
	#test_pickle()
	#test_datalayer()
	test_model()
	test_solver()
	test_solver_branching()
	test_combine()
	test_bv()
	test_simple_merging()
	test_composite_solver()
	test_ite()
	test_bool()
	print "WOO"

	print 'eval', claripy.solvers.solver.cached_evals
	print 'min', claripy.solvers.solver.cached_min
	print 'max', claripy.solvers.solver.cached_max
	print 'solve', claripy.solvers.solver.cached_solve
