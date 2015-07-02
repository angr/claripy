import claripy
import nose

def test_concrete():
    clrp = claripy.Claripies["SerialZ3"]

    a = clrp.BitVecVal(10, 32)
    b = clrp.BoolVal(True)
    c = clrp.BitVec('x', 32)

    nose.tools.assert_is(type(a.model), claripy.BVV)
    nose.tools.assert_is(type(b.model), bool)
    nose.tools.assert_is_instance(c.model, claripy.Base)

if __name__ == '__main__':
    test_concrete()
