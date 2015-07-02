import claripy
import nose

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

if __name__ == '__main__':
    test_model()
