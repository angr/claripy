import claripy
import nose

def test_concrete():
    a = claripy.BitVecVal(10, 32)
    b = claripy.BoolVal(True)
    c = claripy.BitVec('x', 32)

    nose.tools.assert_is(type(a.model), claripy.bv.BVV)
    nose.tools.assert_is(type(b.model), bool)
    nose.tools.assert_is_instance(c.model, claripy.Base)

if __name__ == '__main__':
    test_concrete()
