import nose
import logging
l = logging.getLogger("claripy.test")

import claripy, claripy.backends

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

if __name__ == '__main__':
    import logging
    logging.getLogger('claripy.expression').setLevel(logging.DEBUG)
    logging.getLogger('claripy.backends.backend').setLevel(logging.DEBUG)
    logging.getLogger('claripy.backends.backend_concrete').setLevel(logging.DEBUG)
    logging.getLogger('claripy.backends.backend_abstract').setLevel(logging.DEBUG)
    logging.getLogger('claripy.backends.backend_z3').setLevel(logging.DEBUG)

    test_actualization()
    test_fallback_abstraction()
    print "WOO"
