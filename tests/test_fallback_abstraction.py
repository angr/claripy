import claripy
import nose

def test_fallback_abstraction():
    bz = claripy._backend_z3

    a = claripy.BitVecVal(5, 32)
    b = claripy.BitVec('x', 32, explicit_name=True)
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

    nose.tools.assert_is(type(a.model), claripy.bv.BVV)
    nose.tools.assert_is_instance(b.model, claripy.Base)
    nose.tools.assert_is_instance(c.model, claripy.Base)
    nose.tools.assert_is_instance(d.model, claripy.Base)
    nose.tools.assert_is_instance(e.model, claripy.Base)
    nose.tools.assert_is_instance(f.model, claripy.Base)
    nose.tools.assert_is(type(g.model), claripy.bv.BVV)

    nose.tools.assert_equal(str(b.resolved_with(bz)), 'x')
    nose.tools.assert_equal(b.resolved_with(bz).__module__, 'z3')

    nose.tools.assert_equal(str(c.resolved_with(bz)), '5 + x')
    nose.tools.assert_equal(str(d.resolved_with(bz)), '5 + x')
    nose.tools.assert_equal(str(e.resolved_with(bz)), 'x + 5')
    nose.tools.assert_equal(str(f.resolved_with(bz)), 'x + x')

if __name__ == '__main__':
    test_fallback_abstraction()
