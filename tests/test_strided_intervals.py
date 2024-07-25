# pylint: disable=missing-class-docstring,no-self-use
from __future__ import annotations

import unittest

from claripy.vsa import StridedInterval


def check_si_fields(si, stride, lb, ub):
    lb &= si.max_int(si.bits)
    ub &= si.max_int(si.bits)
    if si.stride != stride:
        return False
    if si.lower_bound != lb:
        return False
    return si.upper_bound == ub


class TestDivision(unittest.TestCase):
    # non-overlapping
    def test_simple_1(self):
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=2)
        # <4>0x1[0x0, 0x1]
        assert check_si_fields(op1.sdiv(op2), 1, 0, 1)
        assert check_si_fields(op1.udiv(op2), 1, 0, 1)

    def test_simple_2(self):
        op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=1)
        # <4>0x1[0xa, 0xc]
        assert check_si_fields(op1.sdiv(op2), 1, 10, 12)
        assert check_si_fields(op1.udiv(op2), 1, 10, 12)

    def test_simple_3(self):
        op1 = StridedInterval(bits=4, stride=1, lower_bound=3, upper_bound=-2)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=-2)
        # udiv:  <4>0x1[0x0, 0x1]
        # sdiv:  <4>0x1[0xc, 0x4]
        assert check_si_fields(op1.udiv(op2), 1, 0, 1)
        assert check_si_fields(op1.sdiv(op2), 1, 12, 4)

    def test_simple_4(self):
        # simple case 4 : Result should be zero
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=0)
        # BOT
        assert op1.sdiv(op2).is_empty
        assert op1.udiv(op2).is_empty

    def test_both_0_hemisphere(self):
        # Both in 0-hemisphere
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=4, upper_bound=6)
        # udiv: <4>0x0[0x0, 0x0]
        # sdiv: <4>0x0[0x0, 0x0]
        assert check_si_fields(op1.udiv(op2), 0, 0, 0)
        assert check_si_fields(op1.sdiv(op2), 0, 0, 0)

    def test_both_1_hemisphere(self):
        # Both in 1-hemisphere
        op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=-3, upper_bound=-1)
        # sdiv: <4>0x1[0x1, 0x6]
        # udiv: <4>0x0[0x0, 0x0]
        assert check_si_fields(op1.sdiv(op2), 1, 1, 6)
        assert check_si_fields(op1.udiv(op2), 0, 0, 0)

    def test_one_0_one_1_hemisphere(self):
        # one in 0-hemisphere and one in 1-hemisphere
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=4)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=-5, upper_bound=-1)
        # sdiv: <4>0x1[0xc, 0xf]
        # udiv: <4>0x0[0x0, 0x0]
        assert check_si_fields(op1.sdiv(op2), 1, 12, 15)
        assert check_si_fields(op1.udiv(op2), 0, 0, 0)

    # Overlapping

    def test_overlapping_both_0_hemisphere(self):
        # case a of figure 2
        # Both in 0-hemisphere
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=6)
        # sdiv: <4>0x1[0x0, 0x3]
        # udiv: <4>0x1[0x0, 0x3]
        assert check_si_fields(op1.sdiv(op2), 1, 0, 3)
        assert check_si_fields(op1.udiv(op2), 1, 0, 3)

    def test_overlapping_both_1_hemisphere(self):
        # Both in 1-hemisphere
        op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=-7, upper_bound=-1)
        # sdiv: <4>0x1[0x0, 0x6]
        # udiv: <4>0x1[0x0, 0x1]
        assert check_si_fields(op1.sdiv(op2), 1, 0, 6)
        assert check_si_fields(op1.udiv(op2), 1, 0, 1)

    def test_overlapping_case_b(self):
        # case b Fig 2
        op1 = StridedInterval(bits=4, stride=1, lower_bound=3, upper_bound=-6)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=7, upper_bound=5)
        # sdiv: <4>0x1[0x0, 0xf]
        # udiv: <4>0x1[0x0, 0xa]
        assert check_si_fields(op1.sdiv(op2), 1, 0, 15)
        assert check_si_fields(op1.udiv(op2), 1, 0, 10)

    def test_overlapping_case_c(self):
        # case c Fig 2
        op1 = StridedInterval(bits=4, stride=1, lower_bound=3, upper_bound=-6)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=5)
        # sdiv: <4>0x1[0x0, 0xe]
        # udiv: <4>0x1[0x0, 0xa]
        assert check_si_fields(op1.sdiv(op2), 1, 0, 14)
        assert check_si_fields(op1.udiv(op2), 1, 0, 10)

    # Strided Tests

    def test_strided_both_0_hemisphere(self):
        # Both in 0-hemisphere
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
        op2 = StridedInterval(bits=4, stride=2, lower_bound=4, upper_bound=6)
        # sdiv: <4>0x0[0x0, 0x0]
        # udiv: <4>0x0[0x0, 0x0]
        assert check_si_fields(op1.sdiv(op2), 0, 0, 0)
        assert check_si_fields(op1.udiv(op2), 0, 0, 0)

    def test_strided_both_1_hemisphere(self):
        # Both in 1-hemisphere
        op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
        op2 = StridedInterval(bits=4, stride=2, lower_bound=-3, upper_bound=-1)
        # sdiv: <4>0x1[0x1, 0x6]
        # udiv: <4>0x0[0x0, 0x0]
        assert check_si_fields(op1.sdiv(op2), 1, 1, 6)
        assert check_si_fields(op1.udiv(op2), 0, 0, 0)

    def test_strided_overlapping_case_1(self):
        # Overlapping case 1
        op1 = StridedInterval(bits=4, stride=2, lower_bound=3, upper_bound=-7)
        op2 = StridedInterval(bits=4, stride=3, lower_bound=7, upper_bound=3)
        # sdiv: <4>0x1[0x9, 0x7]
        # udiv: <4>0x1[0x0, 0x9]
        assert check_si_fields(op1.sdiv(op2), 1, 9, 7)
        assert check_si_fields(op1.udiv(op2), 1, 0, 9)

    def test_strided_overlapping_case_2(self):
        # Overlapping case 2
        op1 = StridedInterval(bits=4, stride=2, lower_bound=3, upper_bound=-7)
        op2 = StridedInterval(bits=4, stride=2, lower_bound=1, upper_bound=3)
        # sdiv: <4>0x1[0x1, 0xd]
        # udiv: <4>0x1[0x1, 0x9]
        assert check_si_fields(op1.sdiv(op2), 1, 1, 13)
        assert check_si_fields(op1.udiv(op2), 1, 1, 9)


class TestMultiplication(unittest.TestCase):
    # non-overlapping
    def test_simple_1(self):
        # simple case 1
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=2)
        # <4>0x2[0x2, 0x6]
        assert check_si_fields(op1.mul(op2), 2, 2, 6)

    def test_simple_2(self):
        # simple case 2
        op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=1)
        # <4>0x1[0xa, 0xc]
        assert check_si_fields(op1.mul(op2), 1, 10, 12)

    def test_simple_3(self):
        # simple case 3
        op1 = StridedInterval(bits=4, stride=1, lower_bound=3, upper_bound=-2)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=-2)
        # Stride should be 2.
        # NOTE: previous result was: <4>0x1[0x4, 0x0] which is wrong.
        # possible values of 1[3,e] * 0[e,e] on 4 bits are [a, 8, 6, 4, 2, 0, e, c]
        # in the previous SI 2 was not present.
        assert check_si_fields(op1.mul(op2), 2, 2, 0)

    def test_simple_4(self):
        # simple case 4 : Result should be zero
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=0)
        # <4>0x0[0x0, 0x0]
        assert check_si_fields(op1.mul(op2), 0, 0, 0)

    def test_both_0_hemisphere(self):
        # simple case 4 : Result should be zero
        # Both in 0-hemisphere
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=4, upper_bound=6)
        # Result: <4>0x1[0x4, 0x2]
        assert check_si_fields(op1.mul(op2), 1, 4, 2)

    def test_both_1_hemisphere(self):
        # Both in 1-hemisphere
        op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=-3, upper_bound=-1)
        # Result <4>0x1[0x4, 0x2]
        assert check_si_fields(op1.mul(op2), 1, 4, 2)

    def test_one_0_one_1_hemisphere(self):
        # one in 0-hemisphere and one in 1-hemisphere
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=4)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=-5, upper_bound=-1)
        # TOP
        assert check_si_fields(op1.mul(op2), 1, 0, 15)

    # Overlapping

    def test_overlapping_both_0_hemisphere(self):
        # case a of figure 2
        # Both in 0-hemisphere
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=6)
        # TOP
        assert check_si_fields(op1.mul(op2), 1, 0, 15)

    def test_overlapping_both_1_hemisphere(self):
        # Both in 1-hemisphere
        op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=-7, upper_bound=-1)
        # TOP
        assert check_si_fields(op1.mul(op2), 1, 0, 15)

    def test_overlapping_case_b(self):
        # case b Fig 2
        op1 = StridedInterval(bits=4, stride=1, lower_bound=3, upper_bound=-6)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=7, upper_bound=5)
        # <4>0x1[0x0, 0xf]
        assert check_si_fields(op1.mul(op2), 1, 0, 15)

    def test_overlapping_case_c(self):
        # case c Fig 2
        op1 = StridedInterval(bits=4, stride=1, lower_bound=3, upper_bound=-6)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=5)
        # <4>0x1[0x0, 0xf]
        assert check_si_fields(op1.mul(op2), 1, 0, 15)

    # Strided Tests

    def test_strided_both_0_hemisphere(self):
        # Both in 0-hemisphere
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
        op2 = StridedInterval(bits=4, stride=2, lower_bound=4, upper_bound=6)
        # <4>0x1[0x4, 0x2]
        assert check_si_fields(op1.mul(op2), 1, 4, 2)

    def test_strided_both_1_hemisphere(self):
        # Both in 1-hemisphere
        op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
        op2 = StridedInterval(bits=4, stride=2, lower_bound=-3, upper_bound=-1)
        # <4>0x1[0x4, 0x2]
        assert check_si_fields(op1.mul(op2), 1, 4, 2)

    def test_strided_overlapping_case_1(self):
        # Overlapping case 1
        op1 = StridedInterval(bits=4, stride=2, lower_bound=3, upper_bound=-7)
        op2 = StridedInterval(bits=4, stride=3, lower_bound=7, upper_bound=3)
        # <4>0x1[0x0, 0xf]
        assert check_si_fields(op1.mul(op2), 1, 0, 15)

    def test_strided_overlapping_case_2(self):
        # Overlapping case 2
        op1 = StridedInterval(bits=4, stride=2, lower_bound=3, upper_bound=-7)
        op2 = StridedInterval(bits=4, stride=2, lower_bound=1, upper_bound=3)
        # TOP
        assert check_si_fields(op1.mul(op2), 1, 0, 15)


class TestSubtraction(unittest.TestCase):
    def test_basic_interval_1(self):
        # Basic Interval Tests
        op1 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=7)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=-6)
        # Result should be TOP
        assert check_si_fields(op1.sub(op2), 1, 0, 15)

    def test_basic_interval_2(self):
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=6)
        # Result should be 1,[-5, 5]
        assert check_si_fields(op1.sub(op2), 1, -5, 5)

    def test_basic_interval_3(self):
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=2)
        # Result should be 1,[15, 5]
        assert check_si_fields(op1.sub(op2), 1, 15, 5)

    def test_basic_interval_4(self):
        op1 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=7)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=2)
        # Result should be 1,[-4, 5]
        assert check_si_fields(op1.sub(op2), 1, -4, 5)

    def test_basic_interval_5(self):
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=0)
        # Result should be 1,[1, 7]
        assert check_si_fields(op1.sub(op2), 1, 1, 7)

    def test_basic_interval_6(self):
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=-5, upper_bound=-1)
        # Result should be 1,[2, 12]
        assert check_si_fields(op1.sub(op2), 1, 2, 12)

    # Strided Tests
    def test_strided_1(self):
        op1 = StridedInterval(bits=4, stride=2, lower_bound=-2, upper_bound=7)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=-6)
        # Result should be TOP
        assert check_si_fields(op1.sub(op2), 1, 0, 15)

    def test_strided_2(self):
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
        op2 = StridedInterval(bits=4, stride=2, lower_bound=2, upper_bound=6)
        # Result should be 1,[11, 5]
        assert check_si_fields(op1.sub(op2), 1, 11, 5)


class TestAddition(unittest.TestCase):
    def test_interval_1(self):
        # Basic Interval Tests
        op1 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=7)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=-6)
        # Result should be TOP
        assert check_si_fields(op1.add(op2), 1, 0, 15)

    def test_interval_2(self):
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=6)
        # Result should be 1,[3, 13]
        assert check_si_fields(op1.add(op2), 1, 3, 13)

    def test_interval_3(self):
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=2)
        # Result should be 1,[3, 9]
        assert check_si_fields(op1.add(op2), 1, 3, 9)

    def test_interval_4(self):
        op1 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=7)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=2)
        # Result should be 1,[0,9]
        assert check_si_fields(op1.add(op2), 1, 0, 9)

    def test_interval_5(self):
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=0)
        # Result should be 1,[1,7]
        assert check_si_fields(op1.add(op2), 1, 1, 7)

    def test_interval_6(self):
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=-5, upper_bound=-1)
        # Result should be 1,[-4, 6]
        assert check_si_fields(op1.add(op2), 1, -4, 6)

    # Strided Tests
    def test_strided_1(self):
        op1 = StridedInterval(bits=4, stride=2, lower_bound=-2, upper_bound=7)
        op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=-6)
        # Result should be TOP
        assert check_si_fields(op1.add(op2), 1, 0, 15)

    def test_strided_2(self):
        op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
        op2 = StridedInterval(bits=4, stride=2, lower_bound=2, upper_bound=6)
        # Result should be 1,[3, 13]
        assert check_si_fields(op1.add(op2), 1, 3, 13)


if __name__ == "__main__":
    unittest.main()
