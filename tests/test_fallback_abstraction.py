import claripy
import nose

def test_fallback_abstraction():
    bz = claripy.backends.z3

    a = claripy.BVV(5, 32)
    b = claripy.BVS('x', 32, explicit_name=True)
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

    nose.tools.assert_is(type(claripy.backends.concrete.convert(a)), claripy.bv.BVV)
    nose.tools.assert_is(type(claripy.backends.concrete.convert(g)), claripy.bv.BVV)

    nose.tools.assert_raises(claripy.errors.BackendError, claripy.backends.concrete.convert, b)
    nose.tools.assert_raises(claripy.errors.BackendError, claripy.backends.concrete.convert, c)
    nose.tools.assert_raises(claripy.errors.BackendError, claripy.backends.concrete.convert, d)
    nose.tools.assert_raises(claripy.errors.BackendError, claripy.backends.concrete.convert, e)
    nose.tools.assert_raises(claripy.errors.BackendError, claripy.backends.concrete.convert, f)

    nose.tools.assert_equal(str(bz.convert(b)), 'x')
    nose.tools.assert_equal(bz.convert(b).__module__, 'z3')

    nose.tools.assert_equal(str(bz.convert(c)), '5 + x')
    nose.tools.assert_equal(str(bz.convert(d)), '5 + x')
    nose.tools.assert_equal(str(bz.convert(e)), 'x + 5')
    nose.tools.assert_equal(str(bz.convert(f)), 'x + x')

if __name__ == '__main__':
    test_fallback_abstraction()
