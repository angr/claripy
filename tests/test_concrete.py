import claripy


def test_concrete():
    a = claripy.BVV(10, 32)
    b = claripy.BoolV(True)
    # c = claripy.BVS('x', 32)

    assert type(claripy.backends.concrete.convert(a)) is claripy.bv.BVV
    assert type(claripy.backends.concrete.convert(b)) is bool

    a = claripy.BVV(1337, 32)
    b = a[31:16]
    c = claripy.BVV(0, 16)
    assert b is c

    bc = claripy.backends.concrete
    d = claripy.BVV(-1, 32)
    assert bc.convert(d) == 0xFFFFFFFF

    e = claripy.BVV(2**32 + 1337, 32)
    assert bc.convert(e) == 1337


def test_concrete_fp():
    f = claripy.FPV(1.0, claripy.FSORT_FLOAT)
    assert claripy.backends.concrete.eval(f, 2) == (1.0,)


if __name__ == "__main__":
    test_concrete()
    test_concrete_fp()
