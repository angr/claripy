import claripy
import nose

def test_concrete():
    a = claripy.BVV(10, 32)
    b = claripy.BoolV(True)
    #c = claripy.BVS('x', 32)

    nose.tools.assert_is(type(claripy.backend_concrete.convert(a)), claripy.bv.BVV)
    nose.tools.assert_is(type(claripy.backend_concrete.convert(b)), bool)

    a = claripy.BVV(1337, 32)
    b = a[31:16]
    c = claripy.BVV(0, 16)
    nose.tools.assert_is(b, c)

if __name__ == '__main__':
    test_concrete()
