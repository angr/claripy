import claripy
import nose

def test_model():
    bc = claripy.backends.concrete

    a = claripy.BVV(5, 32)
    b = claripy.BVS('x', 32, explicit_name=True)
    c = a + b

    r_c = bc.convert(c, result=claripy.Result(True, {'x': 10}))
    nose.tools.assert_equal(r_c, 15)
    r_d = bc.convert(c, result=claripy.Result(True, {'x': 15}))
    nose.tools.assert_equal(r_c, 15)
    nose.tools.assert_equal(r_d, 20)

if __name__ == '__main__':
    test_model()
