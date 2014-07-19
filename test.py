import nose
import logging
l = logging.getLogger("claripy.test")

import pickle
import tempfile
import claripy

import logging
l = logging.getLogger("claripy.test")

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
	clrp = claripy.ClaripyStandalone()
	bc = claripy.backends.BackendConcrete(clrp)
	bz = claripy.backends.BackendZ3(clrp)
	ba = claripy.backends.BackendAbstract(clrp)
	clrp.expression_backends = [ bc, ba, bz ]

	s = clrp.solver()
	x = clrp.BitVec('x', 32)
	y = clrp.BitVec('y', 32)
	z = clrp.BitVec('z', 32)

	l.debug("adding constraints")

	s.add(x == 10)
	s.add(y == 15)
	l.debug("checking")
	nose.tools.assert_equal(s.check(), claripy.sat)
	nose.tools.assert_equal(s.eval(x + 5, 1)[0], 15)

	shards = s.split()
	nose.tools.assert_equal(len(shards), 2)
	nose.tools.assert_equal(len(shards[0].variables), 1)
	nose.tools.assert_equal(len(shards[1].variables), 1)
	nose.tools.assert_equal(len(shards[0].constraints), 1)
	nose.tools.assert_equal(len(shards[1].constraints), 1)

	s = clrp.solver()
	clrp.expression_backends = [ bc, ba, bz ]
	s.add(x > 10)
	s.add(x > 20)
	s.simplify()
	nose.tools.assert_equal(len(s.constraints), 1)
	nose.tools.assert_equal(str(s.constraints[0]._obj), "Not(x <= 20)")

	s.add(y > x)
	s.add(z < 5)

	ss = s.split()
	nose.tools.assert_equal(len(ss), 2)
	nose.tools.assert_equal(len(ss[1].constraints), 1)
	nose.tools.assert_equal(len(ss[0].constraints), 2)

def test_solver_branching():
	clrp = claripy.ClaripyStandalone()
	s = clrp.solver()
	x = clrp.BitVec("x", 32)
	y = clrp.BitVec("y", 32)
	s.add(x > y)
	s.add(x < 10)

	t = s.branch()
	nose.tools.assert_is(s._solver, t._solver)
	nose.tools.assert_true(s._finalized)
	nose.tools.assert_true(t._finalized)
	t.add(x > 5)
	nose.tools.assert_false(s._solver is t._solver)

	s.add(x == 3)
	nose.tools.assert_true(s.check() == claripy.sat)
	t.add(x == 3)
	nose.tools.assert_false(t.check() == claripy.sat)

	s.add(y == 2)
	nose.tools.assert_true(s.check() == claripy.sat)
	nose.tools.assert_equals(s.eval(x, 1)[0], 3)
	nose.tools.assert_equals(s.eval(y, 1)[0], 2)
	nose.tools.assert_false(t.check() == claripy.sat)

if __name__ == '__main__':
	logging.getLogger('claripy.test').setLevel(logging.DEBUG)
	logging.getLogger('claripy.expression').setLevel(logging.DEBUG)
	logging.getLogger('claripy.backends.backend').setLevel(logging.DEBUG)
	logging.getLogger('claripy.backends.backend_concrete').setLevel(logging.DEBUG)
	logging.getLogger('claripy.backends.backend_abstract').setLevel(logging.DEBUG)
	logging.getLogger('claripy.backends.backend_z3').setLevel(logging.DEBUG)
	logging.getLogger('claripy.datalayer').setLevel(logging.DEBUG)
	logging.getLogger('claripy.solvers.core_solver').setLevel(logging.DEBUG)

	test_actualization()
	test_fallback_abstraction()
	test_mixed_z3()
	#test_pickle()
	#test_datalayer()
	test_model()
	test_solver()
	test_solver_branching()
	print "WOO"
