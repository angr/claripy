import nose
import logging
l = logging.getLogger("claripy.test")

import pickle
import tempfile
import claripy, claripy.backends

import logging
l = logging.getLogger("claripy.test")

def test_actualization():
    ba = claripy.backends.BackendAbstract()
    bc = claripy.backends.BackendConcrete()
    a = claripy.E([ba], obj=5, variables=set(), symbolic=False)
    b = a+a
    b.actualize([bc])
    nose.tools.assert_equal(b._obj, 10)

def test_fallback_abstraction():
    ba = claripy.backends.BackendAbstract()
    bc = claripy.backends.BackendConcrete()
    bz = claripy.backends.BackendZ3()

    a = claripy.E([bc, ba], obj=5, variables=set(), symbolic=False)
    b = claripy.E([bc, ba], ast=claripy.A(op='BitVec', args=('x', 32)), variables={'x'}, symbolic=True)
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

    a.actualize([bc, bz])
    nose.tools.assert_equal(str(a._obj), '5')
    nose.tools.assert_is(type(a._obj), int)

    b.actualize([bc, bz])
    nose.tools.assert_equal(str(b._obj), 'x')
    nose.tools.assert_equal(b._obj.__module__, 'z3')

    c.actualize([bc, bz])
    d.actualize([bc, bz])
    e.actualize([bc, bz])
    f.actualize([bc, bz])

    nose.tools.assert_equal(str(c._obj), '5 + x')
    nose.tools.assert_equal(str(d._obj), '5 + x')
    nose.tools.assert_equal(str(e._obj), 'x + 5')
    nose.tools.assert_equal(str(f._obj), 'x + x')

    f._ast = None
    f.abstract([bc, bz])
    f._obj = None
    f.actualize([bc, bz])
    nose.tools.assert_equal(str(f._obj), 'x + x')

def test_mixed_z3():
    ba = claripy.backends.BackendAbstract()
    bc = claripy.backends.BackendConcrete()
    bz = claripy.backends.BackendZ3()

    a = claripy.E([bc, bz, ba], ast=claripy.A(op='BitVecVal', args=(0, 32)), variables=set(), symbolic=False)
    b = claripy.E([bc, bz, ba], ast=claripy.A(op='BitVec', args=('x', 32)), variables={'x'}, symbolic=True)
    c = a+b
    nose.tools.assert_true(b.symbolic)

    a.actualize()
    b.actualize()

    nose.tools.assert_is(type(a._obj), claripy.bv.BVV)
    nose.tools.assert_equal(b._obj.__module__, 'z3')
    nose.tools.assert_is(c._obj, None)

    d = a + b
    nose.tools.assert_equal(d._obj.__module__, 'z3')
    nose.tools.assert_equal(str(d._obj), '0 + x')

    c.actualize()
    nose.tools.assert_equal(c._obj.__module__, 'z3')
    nose.tools.assert_equal(str(c._obj), '0 + x')

def test_pickle():
    ba = claripy.backends.BackendAbstract()
    bc = claripy.backends.BackendConcrete()
    bz = claripy.backends.BackendZ3()

    a = claripy.E([bc, bz, ba], ast=claripy.A(op='BitVecVal', args=(0, 32)), variables=set(), symbolic=False)
    b = claripy.E([bc, bz, ba], ast=claripy.A(op='BitVec', args=('x', 32)), variables={'x'}, symbolic=True)
    a.actualize(); a._ast = None
    b.actualize(); a._ast = None

    c = a+b
    nose.tools.assert_equal(c._obj.__module__, 'z3')
    nose.tools.assert_equal(str(c._obj), '0 + x')

    c_copy = pickle.loads(pickle.dumps(c))
    nose.tools.assert_is(c_copy._obj, None)
    c_copy._backends = [bc, bz, ba]
    c_copy.actualize()
    nose.tools.assert_equal(c_copy._obj.__module__, 'z3')
    nose.tools.assert_equal(str(c_copy._obj), '0 + x')

def test_datalayer():
    l.info("Running test_datalayer")

    ba = claripy.backends.BackendAbstract()
    bc = claripy.backends.BackendConcrete()
    bz = claripy.backends.BackendZ3()
    pickle_dir = tempfile.mkdtemp()
    l.debug("Pickling to %s",pickle_dir)
    claripy.datalayer.init(pickle_dir=pickle_dir)

    a = claripy.E([bc, ba], ast=claripy.A(op='BitVecVal', args=(0, 32)), variables=set(), symbolic=False)
    b = claripy.E([bc, ba], ast=claripy.A(op='BitVec', args=('x', 32)), variables={'x'}, symbolic=True)

    a.actualize(); a._ast = None
    b.store()
    #b.actualize(); b._ast = None
    c = a + b
    c.store()

    c.actualize([ bc, bz ])
    nose.tools.assert_equal(str(c._obj), '0 + x')

    d = a+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b
    d.store()

    l.debug("Loading stage!")
    claripy.datalayer.init(pickle_dir=pickle_dir)
    nose.tools.assert_equal(len(claripy.datalayer.dl._cache), 0)

    e = claripy.datalayer.dl.load_expression(c._uuid)
    e.actualize([ bc, bz ])
    nose.tools.assert_equal(str(e._obj), '0 + x')

if __name__ == '__main__':
    logging.getLogger('claripy.test').setLevel(logging.DEBUG)
    logging.getLogger('claripy.expression').setLevel(logging.DEBUG)
    logging.getLogger('claripy.backends.backend').setLevel(logging.DEBUG)
    logging.getLogger('claripy.backends.backend_concrete').setLevel(logging.DEBUG)
    logging.getLogger('claripy.backends.backend_abstract').setLevel(logging.DEBUG)
    logging.getLogger('claripy.backends.backend_z3').setLevel(logging.DEBUG)
    logging.getLogger('claripy.datalayer').setLevel(logging.DEBUG)

    test_actualization()
    test_fallback_abstraction()
    test_mixed_z3()
    test_pickle()
    test_datalayer()
    print "WOO"
