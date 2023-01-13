import logging

from claripy.vsa import StridedInterval

l = logging.getLogger("angr_tests")


def check_si_fields(si, stride, lb, ub):
    lb &= si.max_int(si.bits)
    ub &= si.max_int(si.bits)
    if si.stride != stride:
        return False
    if si.lower_bound != lb:
        return False
    if si.upper_bound != ub:
        return False
    return True


def test_division():
    # non-overlapping

    # simple case 1
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=2)
    # <4>0x1[0x0, 0x1]
    assert check_si_fields(op1.sdiv(op2), 1, 0, 1)
    assert check_si_fields(op1.udiv(op2), 1, 0, 1)

    # simple case 2
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=1)
    # <4>0x1[0xa, 0xc]
    assert check_si_fields(op1.sdiv(op2), 1, 10, 12)
    assert check_si_fields(op1.udiv(op2), 1, 10, 12)

    # simple case 3
    op1 = StridedInterval(bits=4, stride=1, lower_bound=3, upper_bound=-2)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=-2)
    # udiv:  <4>0x1[0x0, 0x1]
    # sdiv:  <4>0x1[0xc, 0x4]
    assert check_si_fields(op1.udiv(op2), 1, 0, 1)
    assert check_si_fields(op1.sdiv(op2), 1, 12, 4)

    # simple case 4 : Result should be zero
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=0)
    # BOT
    assert op1.sdiv(op2).is_empty
    assert op1.udiv(op2).is_empty

    # Both in 0-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=4, upper_bound=6)
    # udiv: <4>0x0[0x0, 0x0]
    # sdiv: <4>0x0[0x0, 0x0]
    assert check_si_fields(op1.udiv(op2), 0, 0, 0)
    assert check_si_fields(op1.sdiv(op2), 0, 0, 0)

    # Both in 1-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-3, upper_bound=-1)
    # sdiv: <4>0x1[0x1, 0x6]
    # udiv: <4>0x0[0x0, 0x0]
    assert check_si_fields(op1.sdiv(op2), 1, 1, 6)
    assert check_si_fields(op1.udiv(op2), 0, 0, 0)

    # one in 0-hemisphere and one in 1-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=4)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-5, upper_bound=-1)
    # sdiv: <4>0x1[0xc, 0xf]
    # udiv: <4>0x0[0x0, 0x0]
    assert check_si_fields(op1.sdiv(op2), 1, 12, 15)
    assert check_si_fields(op1.udiv(op2), 0, 0, 0)

    # Overlapping

    # case a of figure 2
    # Both in 0-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=6)
    # sdiv: <4>0x1[0x0, 0x3]
    # udiv: <4>0x1[0x0, 0x3]
    assert check_si_fields(op1.sdiv(op2), 1, 0, 3)
    assert check_si_fields(op1.udiv(op2), 1, 0, 3)

    # Both in 1-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-7, upper_bound=-1)
    # sdiv: <4>0x1[0x0, 0x6]
    # udiv: <4>0x1[0x0, 0x1]
    assert check_si_fields(op1.sdiv(op2), 1, 0, 6)
    assert check_si_fields(op1.udiv(op2), 1, 0, 1)

    # case b Fig 2
    op1 = StridedInterval(bits=4, stride=1, lower_bound=3, upper_bound=-6)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=7, upper_bound=5)
    # sdiv: <4>0x1[0x0, 0xf]
    # udiv: <4>0x1[0x0, 0xa]
    assert check_si_fields(op1.sdiv(op2), 1, 0, 15)
    assert check_si_fields(op1.udiv(op2), 1, 0, 10)

    # case c Fig 2
    op1 = StridedInterval(bits=4, stride=1, lower_bound=3, upper_bound=-6)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=5)
    # sdiv: <4>0x1[0x0, 0xe]
    # udiv: <4>0x1[0x0, 0xa]
    assert check_si_fields(op1.sdiv(op2), 1, 0, 14)
    assert check_si_fields(op1.udiv(op2), 1, 0, 10)

    # Strided Tests

    # Both in 0-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
    op2 = StridedInterval(bits=4, stride=2, lower_bound=4, upper_bound=6)
    # sdiv: <4>0x0[0x0, 0x0]
    # udiv: <4>0x0[0x0, 0x0]
    assert check_si_fields(op1.sdiv(op2), 0, 0, 0)
    assert check_si_fields(op1.udiv(op2), 0, 0, 0)

    # Both in 1-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
    op2 = StridedInterval(bits=4, stride=2, lower_bound=-3, upper_bound=-1)
    # sdiv: <4>0x1[0x1, 0x6]
    # udiv: <4>0x0[0x0, 0x0]
    assert check_si_fields(op1.sdiv(op2), 1, 1, 6)
    assert check_si_fields(op1.udiv(op2), 0, 0, 0)

    # Overlapping case 1
    op1 = StridedInterval(bits=4, stride=2, lower_bound=3, upper_bound=-7)
    op2 = StridedInterval(bits=4, stride=3, lower_bound=7, upper_bound=3)
    # sdiv: <4>0x1[0x9, 0x7]
    # udiv: <4>0x1[0x0, 0x9]
    assert check_si_fields(op1.sdiv(op2), 1, 9, 7)
    assert check_si_fields(op1.udiv(op2), 1, 0, 9)

    # Overlapping case 2
    op1 = StridedInterval(bits=4, stride=2, lower_bound=3, upper_bound=-7)
    op2 = StridedInterval(bits=4, stride=2, lower_bound=1, upper_bound=3)
    # sdiv: <4>0x1[0x1, 0xd]
    # udiv: <4>0x1[0x1, 0x9]
    assert check_si_fields(op1.sdiv(op2), 1, 1, 13)
    assert check_si_fields(op1.udiv(op2), 1, 1, 9)


def test_multiplication():
    # non-overlapping

    # simple case 1
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=2)
    # <4>0x2[0x2, 0x6]
    assert check_si_fields(op1.mul(op2), 2, 2, 6)

    # simple case 2
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=1)
    # <4>0x1[0xa, 0xc]
    assert check_si_fields(op1.mul(op2), 1, 10, 12)

    # simple case 3
    op1 = StridedInterval(bits=4, stride=1, lower_bound=3, upper_bound=-2)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=-2)
    # Stride should be 2.
    # NOTE: previous result was: <4>0x1[0x4, 0x0] which is wrong.
    # possible values of 1[3,e] * 0[e,e] on 4 bits are [a, 8, 6, 4, 2, 0, e, c]
    # in the previous SI 2 was not present.
    assert check_si_fields(op1.mul(op2), 2, 2, 0)

    # simple case 4 : Result should be zero
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=0)
    # <4>0x0[0x0, 0x0]
    assert check_si_fields(op1.mul(op2), 0, 0, 0)

    # Both in 0-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=4, upper_bound=6)
    # Result: <4>0x1[0x4, 0x2]
    assert check_si_fields(op1.mul(op2), 1, 4, 2)

    # Both in 1-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-3, upper_bound=-1)
    # Result <4>0x1[0x4, 0x2]
    assert check_si_fields(op1.mul(op2), 1, 4, 2)

    # one in 0-hemisphere and one in 1-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=4)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-5, upper_bound=-1)
    # TOP
    assert check_si_fields(op1.mul(op2), 1, 0, 15)

    # Overlapping

    # case a of figure 2
    # Both in 0-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=6)
    # TOP
    assert check_si_fields(op1.mul(op2), 1, 0, 15)

    # Both in 1-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-7, upper_bound=-1)
    # TOP
    assert check_si_fields(op1.mul(op2), 1, 0, 15)

    # case b Fig 2
    op1 = StridedInterval(bits=4, stride=1, lower_bound=3, upper_bound=-6)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=7, upper_bound=5)
    # <4>0x1[0x0, 0xf]
    assert check_si_fields(op1.mul(op2), 1, 0, 15)

    # case c Fig 2
    op1 = StridedInterval(bits=4, stride=1, lower_bound=3, upper_bound=-6)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=5)
    # <4>0x1[0x0, 0xf]
    assert check_si_fields(op1.mul(op2), 1, 0, 15)

    # Strided Tests

    # Both in 0-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
    op2 = StridedInterval(bits=4, stride=2, lower_bound=4, upper_bound=6)
    # <4>0x1[0x4, 0x2]
    assert check_si_fields(op1.mul(op2), 1, 4, 2)

    # Both in 1-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
    op2 = StridedInterval(bits=4, stride=2, lower_bound=-3, upper_bound=-1)
    # <4>0x1[0x4, 0x2]
    assert check_si_fields(op1.mul(op2), 1, 4, 2)

    # Overlapping case 1
    op1 = StridedInterval(bits=4, stride=2, lower_bound=3, upper_bound=-7)
    op2 = StridedInterval(bits=4, stride=3, lower_bound=7, upper_bound=3)
    # <4>0x1[0x0, 0xf]
    assert check_si_fields(op1.mul(op2), 1, 0, 15)

    # Overlapping case 2
    op1 = StridedInterval(bits=4, stride=2, lower_bound=3, upper_bound=-7)
    op2 = StridedInterval(bits=4, stride=2, lower_bound=1, upper_bound=3)
    # TOP
    assert check_si_fields(op1.mul(op2), 1, 0, 15)


def test_subtraction():
    # Basic Interval Tests
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=-6)
    # Result should be TOP
    assert check_si_fields(op1.sub(op2), 1, 0, 15)

    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=6)
    # Result should be 1,[-5, 5]
    # print(str(op1.sub(op2)))
    assert check_si_fields(op1.sub(op2), 1, -5, 5)

    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=2)
    # Result should be 1,[15, 5]
    assert check_si_fields(op1.sub(op2), 1, 15, 5)

    op1 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=2)
    # Result should be 1,[-4, 5]
    assert check_si_fields(op1.sub(op2), 1, -4, 5)

    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=0)
    # Result should be 1,[1, 7]
    assert check_si_fields(op1.sub(op2), 1, 1, 7)

    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-5, upper_bound=-1)
    # Result should be 1,[2, 12]
    # print(str(op1.sub(op2)))
    assert check_si_fields(op1.sub(op2), 1, 2, 12)

    # Strided Tests
    op1 = StridedInterval(bits=4, stride=2, lower_bound=-2, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=-6)
    # Result should be TOP
    assert check_si_fields(op1.sub(op2), 1, 0, 15)

    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=2, lower_bound=2, upper_bound=6)
    # Result should be 1,[11, 5]
    assert check_si_fields(op1.sub(op2), 1, 11, 5)


def test_add():
    # Basic Interval Tests
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=-6)
    # Result should be TOP
    assert check_si_fields(op1.add(op2), 1, 0, 15)

    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=6)
    # Result should be 1,[3, 13]
    assert check_si_fields(op1.add(op2), 1, 3, 13)

    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=2)
    # Result should be 1,[3, 9]
    assert check_si_fields(op1.add(op2), 1, 3, 9)

    op1 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=2)
    # Result should be 1,[0,9]
    assert check_si_fields(op1.add(op2), 1, 0, 9)

    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=0)
    # Result should be 1,[1,7]
    assert check_si_fields(op1.add(op2), 1, 1, 7)

    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-5, upper_bound=-1)
    # Result should be 1,[-4, 6]
    assert check_si_fields(op1.add(op2), 1, -4, 6)

    # Strided Tests
    op1 = StridedInterval(bits=4, stride=2, lower_bound=-2, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=-6)
    # Result should be TOP
    assert check_si_fields(op1.add(op2), 1, 0, 15)

    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=2, lower_bound=2, upper_bound=6)
    # Result should be 1,[3, 13]
    assert check_si_fields(op1.add(op2), 1, 3, 13)


if __name__ == "__main__":
    # Addition tests
    l.info("Performing Add Tests")
    test_add()
    l.info("Performing Subtraction Tests")
    test_subtraction()
    l.info("Performing Multiplication Tests")
    test_multiplication()
    l.info("Performing Division Tests")
    test_division()
    print("[+] All Tests Passed")
