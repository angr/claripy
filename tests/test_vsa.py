# pylint: disable=missing-class-docstring,no-self-use,no-member
from __future__ import annotations

import unittest

import claripy
from claripy.ast.bv import VS
from claripy.vsa import (
    BoolResult,
    DiscreteStridedIntervalSet,
    StridedInterval,
)


def vsa_model(a):
    return claripy.backends.vsa.convert(a)


class TestVSA(unittest.TestCase):  # pylint: disable=no-member,function-redefined
    def test_fucked_extract(self):
        not_fucked = claripy.Reverse(
            claripy.Concat(
                claripy.BVS("file_/dev/stdin_6_0_16_8", 8, explicit_name=True),
                claripy.BVS("file_/dev/stdin_6_1_17_8", 8, explicit_name=True),
            )
        )
        m = claripy.backends.vsa.max(not_fucked)
        assert m > 0

        zx = claripy.ZeroExt(16, not_fucked)
        pre_fucked = claripy.Reverse(zx)
        m = claripy.backends.vsa.max(pre_fucked)
        assert m > 0

        fucked = pre_fucked[31:16]
        m = claripy.backends.vsa.max(fucked)
        assert m > 0

        # here's another case
        wtf = (
            (
                claripy.Reverse(
                    claripy.Concat(
                        claripy.BVS("w", 8),
                        claripy.BVS("x", 8),
                        claripy.BVS("y", 8),
                        claripy.BVS("z", 8),
                    )
                )
                & claripy.BVV(15, 32)
            )
            + claripy.BVV(48, 32)
        )[7:0]

        m = claripy.backends.vsa.max(wtf)
        assert m > 0

    def test_reversed_concat(self):
        a = claripy.SI("a", 32, lower_bound=10, upper_bound=0x80, stride=10)
        b = claripy.SI("b", 32, lower_bound=1, upper_bound=0xFF, stride=1)

        reversed_a = claripy.Reverse(a)
        reversed_b = claripy.Reverse(b)

        # First let's check if the reversing makes sense
        assert claripy.backends.vsa.min(reversed_a) == 0xA000000
        assert claripy.backends.vsa.max(reversed_a) == 0x80000000
        assert claripy.backends.vsa.min(reversed_b) == 0x1000000
        assert claripy.backends.vsa.max(reversed_b) == 0xFF000000

        a_concat_b = claripy.Concat(a, b)
        assert claripy.backends.vsa.convert(a_concat_b)._reversed is False

        ra_concat_b = claripy.Concat(reversed_a, b)
        assert claripy.backends.vsa.convert(ra_concat_b)._reversed is False

        a_concat_rb = claripy.Concat(a, reversed_b)
        assert claripy.backends.vsa.convert(a_concat_rb)._reversed is False

        ra_concat_rb = claripy.Concat(reversed_a, reversed_b)
        assert claripy.backends.vsa.convert(ra_concat_rb)._reversed is False

    def test_simple_cardinality(self):
        x = claripy.BVS("x", 32, 0xA, 0x14, 0xA)
        assert x.cardinality == 2

    def test_south_pole_splitting(self):
        # south-pole splitting
        si1 = claripy.SI(bits=32, stride=1, lower_bound=-1, upper_bound=1)
        si_list = vsa_model(si1)._ssplit()
        assert len(si_list) == 2
        assert si_list[0].identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=-1, upper_bound=-1)))
        assert si_list[1].identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=1)))

    def test_north_pole_splitting(self):
        # north-pole splitting
        si1 = claripy.SI(bits=32, stride=1, lower_bound=-1, upper_bound=-3)
        si_list = vsa_model(si1)._nsplit()
        assert len(si_list) == 2
        assert si_list[0].identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=-1, upper_bound=0x7FFFFFFF)))
        assert si_list[1].identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=0x80000000, upper_bound=-3)))

    def test_north_pole_ep2_splitting(self):
        # north-pole splitting, episode 2
        si1 = claripy.SI(bits=32, stride=3, lower_bound=3, upper_bound=0)
        si_list = vsa_model(si1)._nsplit()
        assert len(si_list) == 2
        assert si_list[0].identical(vsa_model(claripy.SI(bits=32, stride=3, lower_bound=3, upper_bound=0x7FFFFFFE)))
        assert si_list[1].identical(vsa_model(claripy.SI(bits=32, stride=3, lower_bound=0x80000001, upper_bound=0)))

    def test_bipolar_splitting(self):
        # bipolar splitting
        si1 = claripy.SI(bits=32, stride=1, lower_bound=-2, upper_bound=-8)
        si_list = vsa_model(si1)._psplit()
        assert len(si_list) == 3
        assert si_list[0].identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=-2, upper_bound=-1)))
        assert si_list[1].identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=0x7FFFFFFF)))
        assert si_list[2].identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=0x80000000, upper_bound=-8)))

    def test_plain_addition(self):
        # Plain addition
        si1 = claripy.SI(bits=32, stride=1, lower_bound=-1, upper_bound=1)
        si2 = claripy.SI(bits=32, stride=1, lower_bound=-1, upper_bound=1)
        si3 = claripy.SI(bits=32, stride=1, lower_bound=-2, upper_bound=2)
        assert claripy.backends.vsa.identical(si1 + si2, si3)
        si4 = claripy.SI(bits=32, stride=1, lower_bound=0xFFFFFFFE, upper_bound=2)
        assert claripy.backends.vsa.identical(si1 + si2, si4)
        si5 = claripy.SI(bits=32, stride=1, lower_bound=2, upper_bound=-2)
        assert not claripy.backends.vsa.identical(si1 + si2, si5)

    def test_addition_overflowing_cardinality(self):
        # Addition with overflowing cardinality
        si1 = claripy.SI(bits=8, stride=1, lower_bound=0, upper_bound=0xFE)
        si2 = claripy.SI(bits=8, stride=1, lower_bound=0xFE, upper_bound=0xFF)
        assert vsa_model(si1 + si2).is_top

    def test_addition_without_top(self):
        # Addition that shouldn't get a TOP
        si1 = claripy.SI(bits=8, stride=1, lower_bound=0, upper_bound=0xFE)
        si2 = claripy.SI(bits=8, stride=1, lower_bound=0, upper_bound=0)
        assert not vsa_model(si1 + si2).is_top

    def test_subtraction(self):
        si1 = claripy.SI(bits=8, stride=1, lower_bound=10, upper_bound=15)
        si2 = claripy.SI(bits=8, stride=1, lower_bound=11, upper_bound=12)
        si3 = claripy.SI(bits=8, stride=1, lower_bound=-2, upper_bound=4)
        assert claripy.backends.vsa.identical(si1 - si2, si3)

    def test_integer_multiplication(self):
        # integer multiplication
        si1 = claripy.SI(bits=32, to_conv=0xFFFF)
        si2 = claripy.SI(bits=32, to_conv=0x10000)
        si3 = claripy.SI(bits=32, to_conv=0xFFFF0000)
        assert claripy.backends.vsa.identical(si1 * si2, si3)

    def test_interval_multiplication(self):
        # intervals multiplication
        si1 = claripy.SI(bits=32, stride=1, lower_bound=10, upper_bound=15)
        si2 = claripy.SI(bits=32, stride=1, lower_bound=20, upper_bound=30)
        si3 = claripy.SI(bits=32, stride=1, lower_bound=200, upper_bound=450)
        assert claripy.backends.vsa.identical(si1 * si2, si3)

    def test_integer_division(self):
        # integer division
        si1 = claripy.SI(bits=32, to_conv=10)
        si2 = claripy.SI(bits=32, to_conv=5)
        si3 = claripy.SI(bits=32, to_conv=2)
        assert claripy.backends.vsa.identical(si1 // si2, si3)

        si3 = claripy.SI(bits=32, to_conv=0)
        assert claripy.backends.vsa.identical(si2 // si1, si3)

    def test_interval_division(self):
        # intervals division
        si1 = claripy.SI(bits=32, stride=1, lower_bound=10, upper_bound=100)
        si2 = claripy.SI(bits=32, stride=1, lower_bound=10, upper_bound=20)
        si3 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=10)
        assert claripy.backends.vsa.identical(si1 // si2, si3)

    def test_zero_extension(self):
        # zero-extension
        si1 = claripy.SI(bits=8, stride=1, lower_bound=0, upper_bound=0xFD)
        si_zext = si1.zero_extend(32 - 8)
        si_zext_ = claripy.SI(bits=32, stride=1, lower_bound=0x0, upper_bound=0xFD)
        assert claripy.backends.vsa.identical(si_zext, si_zext_)

    def test_sign_extension(self):
        # sign-extension
        si1 = claripy.SI(bits=8, stride=1, lower_bound=0, upper_bound=0xFD)
        si_sext = si1.sign_extend(32 - 8)
        si_sext_ = claripy.SI(bits=32, stride=1, lower_bound=0xFFFFFF80, upper_bound=0x7F)
        assert claripy.backends.vsa.identical(si_sext, si_sext_)

    def test_comparison_equal(self):
        # -1 == 0xff
        si1 = claripy.SI(bits=8, stride=1, lower_bound=-1, upper_bound=-1)
        si2 = claripy.SI(bits=8, stride=1, lower_bound=0xFF, upper_bound=0xFF)
        assert claripy.backends.vsa.is_true(si1 == si2)

    def test_comparison_not_equal(self):
        # -2 != 0xff
        si1 = claripy.SI(bits=8, stride=1, lower_bound=-2, upper_bound=-2)
        si2 = claripy.SI(bits=8, stride=1, lower_bound=0xFF, upper_bound=0xFF)
        assert claripy.backends.vsa.is_true(si1 != si2)

    def test_comparison_signed_less_than(self):
        # [-2, -1] < [1, 2] (signed arithmetic)
        si1 = claripy.SI(bits=8, stride=1, lower_bound=1, upper_bound=2)
        si2 = claripy.SI(bits=8, stride=1, lower_bound=-2, upper_bound=-1)
        assert claripy.backends.vsa.is_true(si2.SLT(si1))

    def test_comparison_signed_less_equal(self):
        # [-2, -1] <= [1, 2] (signed arithmetic)
        si1 = claripy.SI(bits=8, stride=1, lower_bound=1, upper_bound=2)
        si2 = claripy.SI(bits=8, stride=1, lower_bound=-2, upper_bound=-1)
        assert claripy.backends.vsa.is_true(si2.SLE(si1))

    def test_comparison_unsigned_greater_than(self):
        # [0xfe, 0xff] > [1, 2] (unsigned arithmetic)
        si1 = claripy.SI(bits=8, stride=1, lower_bound=1, upper_bound=2)
        si2 = claripy.SI(bits=8, stride=1, lower_bound=0xFE, upper_bound=0xFF)
        assert claripy.backends.vsa.is_true(si2.UGT(si1))

    def test_comparison_unsigned_greater_equal(self):
        # [0xfe, 0xff] >= [1, 2] (unsigned arithmetic)
        si1 = claripy.SI(bits=8, stride=1, lower_bound=1, upper_bound=2)
        si2 = claripy.SI(bits=8, stride=1, lower_bound=0xFE, upper_bound=0xFF)
        assert claripy.backends.vsa.is_true(si2.UGE(si1))

    def test_wrapped_intervals(self):
        # SI = claripy.StridedInterval

        # Disable the use of DiscreteStridedIntervalSet
        claripy.vsa.strided_interval.allow_dsis = False

        # Signedness/unsignedness conversion
        si1 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=0xFFFFFFFF)
        assert vsa_model(si1)._signed_bounds() == [(0x0, 0x7FFFFFFF), (-0x80000000, -0x1)]
        assert vsa_model(si1)._unsigned_bounds() == [(0x0, 0xFFFFFFFF)]


class TestVSAJoin(unittest.TestCase):  # pylint: disable=no-member,function-redefined

    def setUp(self):
        # Set backend
        self.b = claripy.backends.vsa
        claripy.solver_backends = []

        # Common setup for first two tests
        self.a = claripy.SI(bits=8, to_conv=2)
        self.b = claripy.SI(bits=8, to_conv=10)
        self.c = claripy.SI(bits=8, to_conv=120)
        self.d = claripy.SI(bits=8, to_conv=130)
        self.e = claripy.SI(bits=8, to_conv=132)
        self.f = claripy.SI(bits=8, to_conv=135)

    def test_union_5_elements(self):
        # Test the union of a, b, c, d, e => [2, 132] with a stride of 2
        tmp1 = self.a.union(self.b)
        assert claripy.backends.vsa.identical(tmp1, claripy.SI(bits=8, stride=8, lower_bound=2, upper_bound=10))
        tmp2 = tmp1.union(self.c)
        assert claripy.backends.vsa.identical(tmp2, claripy.SI(bits=8, stride=2, lower_bound=2, upper_bound=120))
        tmp3 = tmp2.union(self.d).union(self.e)
        assert claripy.backends.vsa.identical(tmp3, claripy.SI(bits=8, stride=2, lower_bound=2, upper_bound=132))

    def test_union_6_elements(self):
        # Test the union of a, b, c, d, e, f => [2, 135] with a stride of 1
        tmp = self.a.union(self.b).union(self.c).union(self.d).union(self.e).union(self.f)
        assert claripy.backends.vsa.identical(tmp, claripy.SI(bits=8, stride=1, lower_bound=2, upper_bound=135))

    def test_union_8_elements(self):
        # Test the union of a, b, c, d, e, f, g, h => [220, 135] with a stride of 1
        a = claripy.SI(bits=8, to_conv=1)
        b = claripy.SI(bits=8, to_conv=10)
        c = claripy.SI(bits=8, to_conv=120)
        d = claripy.SI(bits=8, to_conv=130)
        e = claripy.SI(bits=8, to_conv=132)
        f = claripy.SI(bits=8, to_conv=135)
        g = claripy.SI(bits=8, to_conv=220)
        h = claripy.SI(bits=8, to_conv=50)

        tmp = a.union(b).union(c).union(d).union(e).union(f).union(g).union(h)
        assert claripy.backends.vsa.identical(tmp, claripy.SI(bits=8, stride=1, lower_bound=220, upper_bound=135))
        assert 220 in vsa_model(tmp).eval(255)
        assert 225 in vsa_model(tmp).eval(255)
        assert 0 in vsa_model(tmp).eval(255)
        assert 135 in vsa_model(tmp).eval(255)
        assert 138 not in vsa_model(tmp).eval(255)


class TestVSAOperations(unittest.TestCase):  # pylint: disable=no-member function-redefined

    def setUp(self):
        # Set backend
        self.b = claripy.backends.vsa

        # Disable the use of DiscreteStridedIntervalSet
        claripy.vsa.strided_interval.allow_dsis = False

        # Integers
        self.si1 = claripy.SI(bits=32, stride=0, lower_bound=10, upper_bound=10)
        self.si2 = claripy.SI(bits=32, stride=0, lower_bound=10, upper_bound=10)
        self.si3 = claripy.SI(bits=32, stride=0, lower_bound=28, upper_bound=28)

        # Strided intervals
        self.si_a = claripy.SI(bits=32, stride=2, lower_bound=10, upper_bound=20)
        self.si_b = claripy.SI(bits=32, stride=2, lower_bound=-100, upper_bound=200)
        self.si_c = claripy.SI(bits=32, stride=3, lower_bound=-100, upper_bound=200)
        self.si_d = claripy.SI(bits=32, stride=2, lower_bound=50, upper_bound=60)
        self.si_e = claripy.SI(bits=16, stride=1, lower_bound=0x2000, upper_bound=0x3000)
        self.si_f = claripy.SI(bits=16, stride=1, lower_bound=0, upper_bound=255)
        self.si_g = claripy.SI(bits=16, stride=1, lower_bound=0, upper_bound=0xFF)
        self.si_h = claripy.SI(bits=32, stride=0, lower_bound=0x80000000, upper_bound=0x80000000)

    def is_equal(self, ast_0, ast_1):
        return claripy.backends.vsa.identical(ast_0, ast_1)

    def test_tsi_name(self):
        si1 = claripy.TSI(32, name="foo", explicit_name=True)
        assert vsa_model(si1).name == "foo"

    def test_normalization(self):
        # Test for Normalization
        si1_normalized = claripy.SI(bits=32, stride=1, lower_bound=10, upper_bound=10)
        assert vsa_model(si1_normalized).stride == 0

    def test_integers(self):
        # Test for Integers
        assert self.is_equal(self.si1, claripy.SI(bits=32, to_conv=10))
        assert self.is_equal(self.si2, claripy.SI(bits=32, to_conv=10))
        assert self.is_equal(self.si1, self.si2)

    def test_add_operations(self):
        # __add__ operations
        si_add_1 = self.si1 + self.si2
        assert self.is_equal(si_add_1, claripy.SI(bits=32, stride=0, lower_bound=20, upper_bound=20))
        si_add_2 = self.si1 + self.si_a
        assert self.is_equal(si_add_2, claripy.SI(bits=32, stride=2, lower_bound=20, upper_bound=30))
        si_add_3 = self.si_a + self.si_b
        assert self.is_equal(si_add_3, claripy.SI(bits=32, stride=2, lower_bound=-90, upper_bound=220))
        si_add_4 = self.si_b + self.si_c
        assert self.is_equal(si_add_4, claripy.SI(bits=32, stride=1, lower_bound=-200, upper_bound=400))

    def test_add_with_overflow(self):
        # __add__ with overflow
        si_add_5 = self.si_h + 0xFFFFFFFF
        assert self.is_equal(
            si_add_5,
            claripy.SI(bits=32, stride=0, lower_bound=0x7FFFFFFF, upper_bound=0x7FFFFFFF),
        )

    def test_sub_operations(self):
        # __sub__ operations
        si_minus_1 = self.si1 - self.si2
        assert self.is_equal(si_minus_1, claripy.SI(bits=32, stride=0, lower_bound=0, upper_bound=0))
        si_minus_2 = self.si_a - self.si_b
        assert self.is_equal(si_minus_2, claripy.SI(bits=32, stride=2, lower_bound=-190, upper_bound=120))
        si_minus_3 = self.si_b - self.si_c
        assert self.is_equal(si_minus_3, claripy.SI(bits=32, stride=1, lower_bound=-300, upper_bound=300))

    def test_neg_invert(self):
        # __neg__ / __invert__ / bitwise not
        si_neg_1 = ~self.si1
        assert self.is_equal(si_neg_1, claripy.SI(bits=32, to_conv=-11))
        si_neg_2 = ~self.si_b
        assert self.is_equal(si_neg_2, claripy.SI(bits=32, stride=2, lower_bound=-201, upper_bound=99))

    def test_or_operations(self):
        # __or__ operations
        si_or_1 = self.si1 | self.si3
        assert self.is_equal(si_or_1, claripy.SI(bits=32, to_conv=30))
        si_or_2 = self.si1 | self.si2
        assert self.is_equal(si_or_2, claripy.SI(bits=32, to_conv=10))
        si_or_3 = self.si1 | self.si_a  # An integer | a strided interval
        assert self.is_equal(si_or_3, claripy.SI(bits=32, stride=2, lower_bound=10, upper_bound=30))
        si_or_3 = self.si_a | self.si1  # Exchange the operands
        assert self.is_equal(si_or_3, claripy.SI(bits=32, stride=2, lower_bound=10, upper_bound=30))
        si_or_4 = self.si_a | self.si_d  # A strided interval | another strided interval
        assert self.is_equal(si_or_4, claripy.SI(bits=32, stride=2, lower_bound=50, upper_bound=62))
        si_or_4 = self.si_d | self.si_a  # Exchange the operands
        assert self.is_equal(si_or_4, claripy.SI(bits=32, stride=2, lower_bound=50, upper_bound=62))
        si_or_5 = self.si_e | self.si_f
        assert self.is_equal(si_or_5, claripy.SI(bits=16, stride=1, lower_bound=0x2000, upper_bound=0x30FF))
        si_or_6 = self.si_e | self.si_g
        assert self.is_equal(si_or_6, claripy.SI(bits=16, stride=1, lower_bound=0x2000, upper_bound=0x30FF))

    def test_shifting(self):
        # Shifting operations
        si_shl_1 = self.si1 << 3
        assert si_shl_1.size() == 32
        assert self.is_equal(si_shl_1, claripy.SI(bits=32, stride=0, lower_bound=80, upper_bound=80))

    def test_multiplication(self):
        # Multiplication operations
        si_mul_1 = self.si1 * 3
        assert si_mul_1.size() == 32
        assert self.is_equal(si_mul_1, claripy.SI(bits=32, stride=0, lower_bound=30, upper_bound=30))
        si_mul_2 = self.si_a * 3
        assert si_mul_2.size() == 32
        assert self.is_equal(si_mul_2, claripy.SI(bits=32, stride=6, lower_bound=30, upper_bound=60))
        si_mul_3 = self.si_a * self.si_b
        assert si_mul_3.size() == 32
        assert self.is_equal(si_mul_3, claripy.SI(bits=32, stride=2, lower_bound=-2000, upper_bound=4000))

    def test_division(self):
        # Division operations
        si_div_1 = self.si1 // 3
        assert si_div_1.size() == 32
        assert self.is_equal(si_div_1, claripy.SI(bits=32, stride=0, lower_bound=3, upper_bound=3))
        si_div_2 = self.si_a // 3
        assert si_div_2.size() == 32
        assert self.is_equal(si_div_2, claripy.SI(bits=32, stride=1, lower_bound=3, upper_bound=6))

    def test_modulo(self):
        # Modulo operations
        si_mo_1 = self.si1 % 3
        assert si_mo_1.size() == 32
        assert self.is_equal(si_mo_1, claripy.SI(bits=32, stride=0, lower_bound=1, upper_bound=1))
        si_mo_2 = self.si_a % 3
        assert si_mo_2.size() == 32
        assert self.is_equal(si_mo_2, claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=2))

    def test_sign_bit_negative_integer(self):
        # Extracting the sign bit from a negative integer
        si = claripy.SI(bits=64, stride=0, lower_bound=-1, upper_bound=-1)
        sb = si[63:63]
        assert self.is_equal(sb, claripy.SI(bits=1, to_conv=1))

    def test_sign_bit_non_positive_integers(self):
        # Extracting the sign bit from non-positive integers
        si = claripy.SI(bits=64, stride=1, lower_bound=-1, upper_bound=0)
        sb = si[63:63]
        assert self.is_equal(sb, claripy.SI(bits=1, stride=1, lower_bound=0, upper_bound=1))

    def test_extracting_integer(self):
        # Extracting an integer
        si = claripy.SI(
            bits=64,
            stride=0,
            lower_bound=0x7FFFFFFFFFFF0000,
            upper_bound=0x7FFFFFFFFFFF0000,
        )
        part1 = si[63:32]
        part2 = si[31:0]
        assert self.is_equal(
            part1,
            claripy.SI(bits=32, stride=0, lower_bound=0x7FFFFFFF, upper_bound=0x7FFFFFFF),
        )
        assert self.is_equal(
            part2,
            claripy.SI(bits=32, stride=0, lower_bound=0xFFFF0000, upper_bound=0xFFFF0000),
        )

    def test_concatenating_two_integers(self):
        # Concatenating two integers
        si = claripy.SI(
            bits=64,
            stride=0,
            lower_bound=0x7FFFFFFFFFFF0000,
            upper_bound=0x7FFFFFFFFFFF0000,
        )
        part1 = si[63:32]
        part2 = si[31:0]
        si_concat = part1.concat(part2)
        assert self.is_equal(si_concat, si)

    def test_extracting_si(self):
        # Extracting a claripy.SI
        si = claripy.SI(bits=64, stride=0x9, lower_bound=0x1, upper_bound=0xA)
        part1 = si[63:32]
        part2 = si[31:0]
        assert self.is_equal(part1, claripy.SI(bits=32, stride=0, lower_bound=0x0, upper_bound=0x0))
        assert self.is_equal(part2, claripy.SI(bits=32, stride=9, lower_bound=1, upper_bound=10))

    def test_concatenating_two_si(self):
        # Concatenating two claripy.SIs
        si = claripy.SI(bits=64, stride=0x9, lower_bound=0x1, upper_bound=0xA)
        part1 = si[63:32]
        part2 = si[31:0]
        si_concat = part1.concat(part2)
        assert self.is_equal(si_concat, si)

    def test_concatenating_two_si_different_sizes(self):
        # Concatenating two SIs that are of different sizes
        si_1 = claripy.SI(bits=64, stride=1, lower_bound=0, upper_bound=0xFFFFFFFFFFFFFFFF)
        si_2 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=0xFFFFFFFF)
        si_concat = si_1.concat(si_2)
        assert self.is_equal(
            si_concat,
            claripy.SI(bits=96, stride=1, lower_bound=0, upper_bound=0xFFFFFFFFFFFFFFFFFFFFFFFF),
        )

    def test_zero_extend(self):
        # Zero-Extend the low part
        si = claripy.SI(bits=64, stride=0x9, lower_bound=0x1, upper_bound=0xA)
        part2 = si[31:0]
        si_zeroextended = part2.zero_extend(32)
        assert self.is_equal(si_zeroextended, claripy.SI(bits=64, stride=9, lower_bound=1, upper_bound=10))

    def test_sign_extend(self):
        # Sign-extension
        si = claripy.SI(bits=64, stride=0x9, lower_bound=0x1, upper_bound=0xA)
        part2 = si[31:0]
        si_signextended = part2.sign_extend(32)
        assert self.is_equal(si_signextended, claripy.SI(bits=64, stride=9, lower_bound=1, upper_bound=10))

    def test_extract_from_zero_extended(self):
        # Extract from the result above
        si = claripy.SI(bits=64, stride=0x9, lower_bound=0x1, upper_bound=0xA)
        part2 = si[31:0]
        si_zeroextended = part2.zero_extend(32)
        si_extracted = si_zeroextended[31:0]
        assert self.is_equal(si_extracted, claripy.SI(bits=32, stride=9, lower_bound=1, upper_bound=10))

    def test_union_operations(self):
        # Union operations
        si_union_1 = self.si1.union(self.si2)
        assert self.is_equal(si_union_1, claripy.SI(bits=32, stride=0, lower_bound=10, upper_bound=10))

        si_union_2 = self.si1.union(self.si3)
        assert self.is_equal(si_union_2, claripy.SI(bits=32, stride=18, lower_bound=10, upper_bound=28))

        si_union_3 = self.si1.union(self.si_a)
        assert self.is_equal(si_union_3, claripy.SI(bits=32, stride=2, lower_bound=10, upper_bound=20))

        si_union_4 = self.si_a.union(self.si_b)
        assert self.is_equal(si_union_4, claripy.SI(bits=32, stride=2, lower_bound=-100, upper_bound=200))

        si_union_5 = self.si_b.union(self.si_c)
        assert self.is_equal(si_union_5, claripy.SI(bits=32, stride=1, lower_bound=-100, upper_bound=200))

    def test_intersection_operations(self):
        # Intersection operations
        si_intersection_1 = self.si1.intersection(self.si1)
        assert self.is_equal(si_intersection_1, self.si2)

        si_intersection_2 = self.si1.intersection(self.si2)
        assert self.is_equal(si_intersection_2, claripy.SI(bits=32, stride=0, lower_bound=10, upper_bound=10))

        si_intersection_3 = self.si1.intersection(self.si_a)
        assert self.is_equal(si_intersection_3, claripy.SI(bits=32, stride=0, lower_bound=10, upper_bound=10))

        si_intersection_4 = self.si_a.intersection(self.si_b)
        assert self.is_equal(si_intersection_4, claripy.SI(bits=32, stride=2, lower_bound=10, upper_bound=20))

        si_intersection_5 = self.si_b.intersection(self.si_c)
        assert self.is_equal(
            si_intersection_5,
            claripy.SI(bits=32, stride=6, lower_bound=-100, upper_bound=200),
        )

    def test_more_intersections(self):
        # More intersections
        t0 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=0x27)
        t1 = claripy.SI(bits=32, stride=0x7FFFFFFF, lower_bound=0x80000002, upper_bound=1)

        si_is_6 = t0.intersection(t1)
        assert self.is_equal(si_is_6, claripy.SI(bits=32, stride=0, lower_bound=1, upper_bound=1))

        t2 = claripy.SI(bits=32, stride=5, lower_bound=20, upper_bound=30)
        t3 = claripy.SI(bits=32, stride=1, lower_bound=27, upper_bound=0xFFFFFFFF)

        si_is_7 = t2.intersection(t3)
        assert self.is_equal(si_is_7, claripy.SI(bits=32, stride=0, lower_bound=30, upper_bound=30))

        t4 = claripy.SI(bits=32, stride=5, lower_bound=-400, upper_bound=400)
        t5 = claripy.SI(bits=32, stride=1, lower_bound=395, upper_bound=-395)

        si_is_8 = t4.intersection(t5)
        assert self.is_equal(si_is_8, claripy.SI(bits=32, stride=5, lower_bound=-400, upper_bound=400))

    def test_sign_extension(self):
        # Sign-extension
        si = claripy.SI(bits=1, stride=0, lower_bound=1, upper_bound=1)
        si_signextended = si.sign_extend(31)
        assert self.is_equal(
            si_signextended,
            claripy.SI(bits=32, stride=0, lower_bound=0xFFFFFFFF, upper_bound=0xFFFFFFFF),
        )

    def test_comparison_si_bvv(self):
        # Comparison between claripy.SI and BVV
        si = claripy.SI(bits=32, stride=1, lower_bound=-0x7F, upper_bound=0x7F)
        claripy.backends.vsa.convert(si).uninitialized = True
        bvv = claripy.BVV(0x30, 32)
        comp = si < bvv
        assert claripy.backends.vsa.convert(comp).identical(claripy.vsa.MaybeResult())

    def test_better_extraction(self):
        # Better extraction
        si = claripy.SI(bits=32, stride=0x1000000, lower_bound=0xCFFFFFF, upper_bound=0xDFFFFFF)
        si_byte0 = si[7:0]
        si_byte1 = si[15:8]
        si_byte2 = si[23:16]
        si_byte3 = si[31:24]
        assert self.is_equal(si_byte0, claripy.SI(bits=8, stride=0, lower_bound=0xFF, upper_bound=0xFF))
        assert self.is_equal(si_byte1, claripy.SI(bits=8, stride=0, lower_bound=0xFF, upper_bound=0xFF))
        assert self.is_equal(si_byte2, claripy.SI(bits=8, stride=0, lower_bound=0xFF, upper_bound=0xFF))
        assert self.is_equal(si_byte3, claripy.SI(bits=8, stride=1, lower_bound=0xC, upper_bound=0xD))

    def test_bitwise_and_optimization(self):
        # Optimization on bitwise-and
        si_1 = claripy.SI(bits=32, stride=1, lower_bound=0x0, upper_bound=0xFFFFFFFF)
        si_2 = claripy.SI(bits=32, stride=0, lower_bound=0x80000000, upper_bound=0x80000000)
        si = si_1 & si_2
        assert self.is_equal(
            si,
            claripy.SI(bits=32, stride=0x80000000, lower_bound=0, upper_bound=0x80000000),
        )

        si_1 = claripy.SI(bits=32, stride=1, lower_bound=0x0, upper_bound=0x7FFFFFFF)
        si_2 = claripy.SI(bits=32, stride=0, lower_bound=0x80000000, upper_bound=0x80000000)
        si = si_1 & si_2
        assert self.is_equal(si, claripy.SI(bits=32, stride=0, lower_bound=0, upper_bound=0))

    def test_concatenation_with_zeros(self):
        # Concatenation: concat with zeros only increases the stride
        si_1 = claripy.SI(bits=8, stride=0xFF, lower_bound=0x0, upper_bound=0xFF)
        si_2 = claripy.SI(bits=8, stride=0, lower_bound=0, upper_bound=0)
        si = si_1.concat(si_2)
        assert self.is_equal(si, claripy.SI(bits=16, stride=0xFF00, lower_bound=0, upper_bound=0xFF00))

    def test_extraction_from_reversed_value(self):
        # Extract from a reversed value
        si_1 = claripy.SI(bits=64, stride=0xFF, lower_bound=0x0, upper_bound=0xFF)
        si_2 = si_1.reversed[63:56]
        assert self.is_equal(si_2, claripy.SI(bits=8, stride=0xFF, lower_bound=0x0, upper_bound=0xFF))

    def test_value_set_operations(self):
        # ValueSet operations
        vs_1 = VS(bits=32, value=0)
        vs_1 = vs_1.intersection(VS(bits=32, value=1))
        assert vsa_model(vs_1).is_empty

        # Test merging two addresses
        vsa_model(vs_1)._merge_si("global", 0, vsa_model(claripy.SI(bits=32, stride=0, lower_bound=10, upper_bound=10)))
        vsa_model(vs_1)._merge_si("global", 0, vsa_model(claripy.SI(bits=32, stride=0, lower_bound=28, upper_bound=28)))
        assert (
            vsa_model(vs_1)
            .get_si("global")
            .identical(vsa_model(claripy.SI(bits=32, stride=18, lower_bound=10, upper_bound=28)))
        )
        assert len(vsa_model(vs_1)) == 32

        vs_1 = VS(name="boo", bits=32, value=0).intersection(VS(name="makeitempty", bits=32, value=1))
        vs_2 = VS(name="foo", bits=32, value=0).intersection(VS(name="makeitempty", bits=32, value=1))
        assert self.is_equal(vs_1, vs_1)
        assert self.is_equal(vs_2, vs_2)
        vsa_model(vs_1)._merge_si("global", 0, vsa_model(claripy.SI(bits=32, stride=0, lower_bound=10, upper_bound=10)))
        assert not self.is_equal(vs_1, vs_2)
        vsa_model(vs_2)._merge_si("global", 0, vsa_model(claripy.SI(bits=32, stride=0, lower_bound=10, upper_bound=10)))
        assert self.is_equal(vs_1, vs_2)
        assert claripy.backends.vsa.is_true((vs_1 & vs_2) == vs_1)
        vsa_model(vs_1)._merge_si(
            "global", 0, vsa_model(claripy.SI(bits=32, stride=18, lower_bound=10, upper_bound=28))
        )
        assert not self.is_equal(vs_1, vs_2)

    def test_value_set_subtraction(self):
        # Subtraction of two pointers yields a concrete value
        vs_1 = claripy.ValueSet(name="foo", region="global", bits=32, value=0x400010)
        vs_2 = claripy.ValueSet(name="bar", region="global", bits=32, value=0x400000)
        si = vs_1 - vs_2
        # assert isinstance(vsa_model(si), claripy.SI)
        assert type(vsa_model(si)) is StridedInterval

        assert self.is_equal(si, claripy.SI(bits=32, stride=0, lower_bound=0x10, upper_bound=0x10))

    def test_if_proxy(self):
        # IfProxy
        si = claripy.SI(bits=32, stride=1, lower_bound=10, upper_bound=0xFFFFFFFF)
        if_0 = claripy.If(si == 0, si, si - 1)
        assert self.is_equal(if_0, if_0)
        assert not self.is_equal(if_0, si)

    def test_max_min_on_ifproxy(self):
        # max and min on IfProxy
        si = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=0xFFFFFFFF)
        if_0 = claripy.If(si == 0, si, si - 1)
        max_val = self.b.max(if_0)
        min_val = self.b.min(if_0)
        assert max_val == 0xFFFFFFFF
        assert min_val == 0x00000000

    def test_if_proxy_identical(self):
        # identical
        si = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=0xFFFFFFFF)
        if_0 = claripy.If(si == 0, si, si - 1)
        if_0_copy = claripy.If(si == 0, si, si - 1)
        assert self.is_equal(if_0, if_0_copy)
        if_1 = claripy.If(si == 1, si, si - 1)
        assert self.is_equal(if_0, if_1)

        si = claripy.SI(bits=32, stride=0, lower_bound=1, upper_bound=1)
        if_0 = claripy.If(si == 0, si, si - 1)
        if_0_copy = claripy.If(si == 0, si, si - 1)
        assert self.is_equal(if_0, if_0_copy)
        if_1 = claripy.If(si == 1, si, si - 1)
        assert not self.is_equal(if_0, if_1)
        if_1 = claripy.If(si == 0, si + 1, si - 1)
        assert self.is_equal(if_0, if_1)
        if_1 = claripy.If(si == 0, si, si)
        assert not self.is_equal(if_0, if_1)

    def test_if_proxy_and_operations(self):
        # if_1 = And(VS_2, IfProxy(si == 0, 0, 1))
        vs_2 = claripy.ValueSet(region="global", bits=32, value=0xFA7B00B)
        si = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=1)
        if_1 = vs_2 & claripy.If(
            si == 0,
            claripy.SI(bits=32, stride=0, lower_bound=0, upper_bound=0),
            claripy.SI(bits=32, stride=0, lower_bound=0xFFFFFFFF, upper_bound=0xFFFFFFFF),
        )
        assert claripy.backends.vsa.is_true(
            vsa_model(if_1.ite_excavated.args[1]) == vsa_model(claripy.ValueSet(region="global", bits=32, value=0))
        )
        assert claripy.backends.vsa.is_true(vsa_model(if_1.ite_excavated.args[2]) == vsa_model(vs_2))

    def test_if_proxy_or_operations(self):
        # if_2 = And(VS_3, IfProxy(si != 0, 0, 1))
        vs_3 = claripy.ValueSet(region="global", bits=32, value=0xDEADCA7)
        si = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=1)
        if_2 = vs_3 & claripy.If(
            si != 0,
            claripy.SI(bits=32, stride=0, lower_bound=0, upper_bound=0),
            claripy.SI(bits=32, stride=0, lower_bound=0xFFFFFFFF, upper_bound=0xFFFFFFFF),
        )
        assert claripy.backends.vsa.is_true(
            vsa_model(if_2.ite_excavated.args[1]) == vsa_model(claripy.ValueSet(region="global", bits=32, value=0))
        )
        assert claripy.backends.vsa.is_true(vsa_model(if_2.ite_excavated.args[2]) == vsa_model(vs_3))

    # Something crazy is gonna happen...
    # if_3 = if_1 + if_2
    # assert claripy.backends.vsa.is_true(vsa_model(if_3.ite_excavated.args[1]) == vsa_model(vs_3)))
    # assert claripy.backends.vsa.is_true(vsa_model(if_3.ite_excavated.args[1]) == vsa_model(vs_2)))


class TestVSAConstraintToSI(unittest.TestCase):  # pylint: disable=no-member,function-redefined

    def setUp(self):
        self.b = claripy.backends.vsa
        self.s = claripy.SolverVSA()  # pylint:disable=unused-variable
        claripy.vsa.strided_interval.allow_dsis = False

    def test_if_si_equals_1(self):
        # If(SI == 0, 1, 0) == 1
        s1 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=2)
        ast_true = claripy.If(s1 == claripy.BVV(0, 32), claripy.BVV(1, 1), claripy.BVV(0, 1)) == claripy.BVV(1, 1)
        ast_false = claripy.If(s1 == claripy.BVV(0, 32), claripy.BVV(1, 1), claripy.BVV(0, 1)) != claripy.BVV(1, 1)

        trueside_sat, trueside_replacement = self.b.constraint_to_si(ast_true)
        assert trueside_sat
        assert len(trueside_replacement) == 1
        assert trueside_replacement[0][0] is s1
        # True side: claripy.SI<32>0[0, 0]
        assert claripy.backends.vsa.is_true(
            trueside_replacement[0][1] == claripy.SI(bits=32, stride=0, lower_bound=0, upper_bound=0)
        )

        falseside_sat, falseside_replacement = self.b.constraint_to_si(ast_false)
        assert falseside_sat is True
        assert len(falseside_replacement) == 1
        assert falseside_replacement[0][0] is s1
        # False side; claripy.SI<32>1[1, 2]
        assert claripy.backends.vsa.identical(
            falseside_replacement[0][1], claripy.SI(bits=32, stride=1, lower_bound=1, upper_bound=2)
        )

    def test_if_si_less_than_or_equal_1(self):
        # If(SI == 0, 1, 0) <= 1
        s1 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=2)
        ast_true = claripy.If(s1 == claripy.BVV(0, 32), claripy.BVV(1, 1), claripy.BVV(0, 1)) <= claripy.BVV(1, 1)
        ast_false = claripy.If(s1 == claripy.BVV(0, 32), claripy.BVV(1, 1), claripy.BVV(0, 1)) > claripy.BVV(1, 1)

        trueside_sat, trueside_replacement = self.b.constraint_to_si(ast_true)
        assert trueside_sat  # Always satisfiable

        falseside_sat, falseside_replacement = self.b.constraint_to_si(ast_false)
        assert not falseside_sat  # Not satisfiable

    def test_if_si_greater_than_15(self):
        # If(SI == 0, 20, 10) > 15
        s1 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=2)
        ast_true = claripy.If(s1 == claripy.BVV(0, 32), claripy.BVV(20, 32), claripy.BVV(10, 32)) > claripy.BVV(15, 32)
        ast_false = claripy.If(s1 == claripy.BVV(0, 32), claripy.BVV(20, 32), claripy.BVV(10, 32)) <= claripy.BVV(
            15, 32
        )

        trueside_sat, trueside_replacement = self.b.constraint_to_si(ast_true)
        assert trueside_sat
        assert len(trueside_replacement) == 1
        assert trueside_replacement[0][0] is s1
        # True side: SI<32>0[0, 0]
        assert claripy.backends.vsa.identical(
            trueside_replacement[0][1], claripy.SI(bits=32, stride=0, lower_bound=0, upper_bound=0)
        )

        falseside_sat, falseside_replacement = self.b.constraint_to_si(ast_false)
        assert falseside_sat
        assert len(falseside_replacement) == 1
        assert falseside_replacement[0][0] is s1
        # False side; SI<32>1[1, 2]
        assert claripy.backends.vsa.identical(
            falseside_replacement[0][1], claripy.SI(bits=32, stride=1, lower_bound=1, upper_bound=2)
        )

    def test_if_si_greater_than_or_equal_15(self):
        # If(SI == 0, 20, 10) >= 15
        s1 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=2)
        ast_true = claripy.If(s1 == claripy.BVV(0, 32), claripy.BVV(15, 32), claripy.BVV(10, 32)) >= claripy.BVV(15, 32)
        ast_false = claripy.If(s1 == claripy.BVV(0, 32), claripy.BVV(15, 32), claripy.BVV(10, 32)) < claripy.BVV(15, 32)

        trueside_sat, trueside_replacement = self.b.constraint_to_si(ast_true)
        assert trueside_sat
        assert len(trueside_replacement) == 1
        assert trueside_replacement[0][0] is s1
        # True side: SI<32>0[0, 0]
        assert claripy.backends.vsa.identical(
            trueside_replacement[0][1], claripy.SI(bits=32, stride=0, lower_bound=0, upper_bound=0)
        )

        falseside_sat, falseside_replacement = self.b.constraint_to_si(ast_false)
        assert falseside_sat
        assert len(falseside_replacement) == 1
        assert falseside_replacement[0][0] is s1
        # False side; SI<32>0[0,0]
        assert claripy.backends.vsa.identical(
            falseside_replacement[0][1], claripy.SI(bits=32, stride=1, lower_bound=1, upper_bound=2)
        )

    def test_extract_and_concat(self):
        # Extract(0, 0, Concat(BVV(0, 63), If(SI == 0, 1, 0))) == 1
        s2 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=2)
        ast_true = (
            claripy.Extract(
                0, 0, claripy.Concat(claripy.BVV(0, 63), claripy.If(s2 == 0, claripy.BVV(1, 1), claripy.BVV(0, 1)))
            )
            == 1
        )
        ast_false = (
            claripy.Extract(
                0, 0, claripy.Concat(claripy.BVV(0, 63), claripy.If(s2 == 0, claripy.BVV(1, 1), claripy.BVV(0, 1)))
            )
            != 1
        )

        trueside_sat, trueside_replacement = self.b.constraint_to_si(ast_true)
        assert trueside_sat
        assert len(trueside_replacement) == 1
        assert trueside_replacement[0][0] is s2
        # True side: claripy.SI<32>0[0, 0]
        assert claripy.backends.vsa.identical(
            trueside_replacement[0][1], claripy.SI(bits=32, stride=0, lower_bound=0, upper_bound=0)
        )

        falseside_sat, falseside_replacement = self.b.constraint_to_si(ast_false)
        assert falseside_sat
        assert len(falseside_replacement) == 1
        assert falseside_replacement[0][0] is s2
        # False side; claripy.SI<32>1[1, 2]
        assert claripy.backends.vsa.identical(
            falseside_replacement[0][1], claripy.SI(bits=32, stride=1, lower_bound=1, upper_bound=2)
        )

    def test_zero_extend_and_extract(self):
        # Extract(0, 0, ZeroExt(32, If(SI == 0, BVV(1, 32), BVV(0, 32)))) == 1
        s3 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=2)
        ast_true = (
            claripy.Extract(0, 0, claripy.ZeroExt(32, claripy.If(s3 == 0, claripy.BVV(1, 32), claripy.BVV(0, 32)))) == 1
        )
        ast_false = (
            claripy.Extract(0, 0, claripy.ZeroExt(32, claripy.If(s3 == 0, claripy.BVV(1, 32), claripy.BVV(0, 32)))) != 1
        )

        trueside_sat, trueside_replacement = self.b.constraint_to_si(ast_true)
        assert trueside_sat
        assert len(trueside_replacement) == 1
        assert trueside_replacement[0][0] is s3
        # True side: claripy.SI<32>0[0, 0]
        assert claripy.backends.vsa.identical(
            trueside_replacement[0][1], claripy.SI(bits=32, stride=0, lower_bound=0, upper_bound=0)
        )

        falseside_sat, falseside_replacement = self.b.constraint_to_si(ast_false)
        assert falseside_sat
        assert len(falseside_replacement) == 1
        assert falseside_replacement[0][0] is s3
        # False side; claripy.SI<32>1[1, 2]
        assert claripy.backends.vsa.identical(
            falseside_replacement[0][1], claripy.SI(bits=32, stride=1, lower_bound=1, upper_bound=2)
        )

    def test_extract_zero_extend_if_expr(self):
        # Extract(0, 0, ZeroExt(32, If(Extract(32, 0, (SI & claripy.SI)) < 0, BVV(1, 1), BVV(0, 1))))
        s4 = claripy.SI(bits=64, stride=1, lower_bound=0, upper_bound=0xFFFFFFFFFFFFFFFF)
        ast_true = (
            claripy.Extract(
                0,
                0,
                claripy.ZeroExt(
                    32,
                    claripy.If(claripy.Extract(31, 0, (s4 & s4)).SLT(0), claripy.BVV(1, 32), claripy.BVV(0, 32)),
                ),
            )
            == 1
        )
        ast_false = (
            claripy.Extract(
                0,
                0,
                claripy.ZeroExt(
                    32,
                    claripy.If(claripy.Extract(31, 0, (s4 & s4)).SLT(0), claripy.BVV(1, 32), claripy.BVV(0, 32)),
                ),
            )
            != 1
        )

        trueside_sat, trueside_replacement = self.b.constraint_to_si(ast_true)
        assert trueside_sat
        assert len(trueside_replacement) == 1
        assert trueside_replacement[0][0] is s4[31:0]
        # True side: claripy.SI<32>0[0, 0]
        assert claripy.backends.vsa.identical(
            trueside_replacement[0][1],
            claripy.SI(bits=32, stride=1, lower_bound=-0x80000000, upper_bound=-1),
        )

        falseside_sat, falseside_replacement = self.b.constraint_to_si(ast_false)
        assert falseside_sat
        assert len(falseside_replacement) == 1
        assert falseside_replacement[0][0] is s4[31:0]
        # False side; claripy.SI<32>1[1, 2]
        assert claripy.backends.vsa.identical(
            falseside_replacement[0][1],
            claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=0x7FFFFFFF),
        )

    def test_top_si_not_equal_neg1(self):
        # TOP_SI != -1
        s5 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=0xFFFFFFFF)
        ast_true = s5 == claripy.SI(bits=32, stride=1, lower_bound=0xFFFFFFFF, upper_bound=0xFFFFFFFF)
        ast_false = s5 != claripy.SI(bits=32, stride=1, lower_bound=0xFFFFFFFF, upper_bound=0xFFFFFFFF)

        trueside_sat, trueside_replacement = self.b.constraint_to_si(ast_true)
        assert trueside_sat
        assert len(trueside_replacement) == 1
        assert trueside_replacement[0][0] is s5
        # True side: claripy.SI<32>0xFFFFFFFF[0xFFFFFFFF, 0xFFFFFFFF]
        assert claripy.backends.vsa.identical(
            trueside_replacement[0][1],
            claripy.SI(bits=32, stride=1, lower_bound=0xFFFFFFFF, upper_bound=0xFFFFFFFF),
        )

        falseside_sat, falseside_replacement = self.b.constraint_to_si(ast_false)
        assert falseside_sat
        assert len(falseside_replacement) == 1
        assert falseside_replacement[0][0] is s5
        # False side: claripy.SI<32>0xFFFFFFFF[0, 0xFFFFFFFE]
        assert claripy.backends.vsa.identical(
            falseside_replacement[0][1],
            claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=0xFFFFFFFE),
        )

    #     # TODO: Add some more insane test cases


class TestVSADiscreteValueSet(unittest.TestCase):  # pylint: disable=no-member,function-redefined

    def setUp(self):
        # Set backend
        self.b = claripy.backends.vsa
        self.s = claripy.SolverVSA()  # pylint:disable=unused-variable

        # Allow the use of DiscreteStridedIntervalSet
        claripy.vsa.strided_interval.allow_dsis = True

    def tearDown(self):
        # Disable DiscreteStridedIntervalSet after tests
        claripy.vsa.strided_interval.allow_dsis = False

    def test_union_operations(self):
        # Union operations
        val_1 = claripy.BVV(0, 32)
        val_2 = claripy.BVV(1, 32)
        r = val_1.union(val_2)
        assert isinstance(vsa_model(r), DiscreteStridedIntervalSet)
        assert vsa_model(r).collapse().identical(StridedInterval(bits=32, stride=1, lower_bound=0, upper_bound=1))

        r = r.union(claripy.BVV(3, 32))
        ints = self.b.eval(r, 4)
        assert len(ints) == 3
        assert ints == [0, 1, 3]

    def test_intersection_operations(self):
        # Intersection operations
        val_1 = claripy.BVV(0, 32)
        val_2 = claripy.BVV(1, 32)
        r = val_1.intersection(val_2)
        assert isinstance(vsa_model(r), StridedInterval)
        assert vsa_model(r).is_empty

        val_1 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=10)
        val_2 = claripy.SI(bits=32, stride=1, lower_bound=10, upper_bound=20)
        val_3 = claripy.SI(bits=32, stride=1, lower_bound=15, upper_bound=50)
        r = val_1.union(val_2)
        assert isinstance(vsa_model(r), DiscreteStridedIntervalSet)
        r = r.intersection(val_3)
        assert sorted(self.b.eval(r, 100)) == [15, 16, 17, 18, 19, 20]

    def test_logical_operations(self):
        # Logical operations
        val_1 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=10)
        val_2 = claripy.SI(bits=32, stride=1, lower_bound=5, upper_bound=20)
        r_1 = val_1.union(val_2)
        val_3 = claripy.SI(bits=32, stride=1, lower_bound=20, upper_bound=30)
        val_4 = claripy.SI(bits=32, stride=1, lower_bound=25, upper_bound=35)
        r_2 = val_3.union(val_4)
        assert isinstance(vsa_model(r_1), DiscreteStridedIntervalSet)
        assert isinstance(vsa_model(r_2), DiscreteStridedIntervalSet)

        # Perform logical comparisons
        assert BoolResult.is_maybe(vsa_model(r_1 < r_2))
        assert BoolResult.is_true(vsa_model(r_1 <= r_2))
        assert BoolResult.is_maybe(vsa_model(r_1 >= r_2))
        assert BoolResult.is_false(vsa_model(r_1 > r_2))
        assert BoolResult.is_maybe(vsa_model(r_1 == r_2))
        assert BoolResult.is_maybe(vsa_model(r_1 != r_2))

    def test_arithmetic_operations(self):
        # Arithmetic operations
        val_1 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=10)
        val_2 = claripy.SI(bits=32, stride=1, lower_bound=5, upper_bound=20)
        r_1 = val_1.union(val_2)
        val_3 = claripy.SI(bits=32, stride=1, lower_bound=20, upper_bound=30)
        val_4 = claripy.SI(bits=32, stride=1, lower_bound=25, upper_bound=35)
        r_2 = val_3.union(val_4)
        assert isinstance(vsa_model(r_1), DiscreteStridedIntervalSet)
        assert isinstance(vsa_model(r_2), DiscreteStridedIntervalSet)

        # Addition
        r = r_1 + r_2
        assert isinstance(vsa_model(r), DiscreteStridedIntervalSet)
        assert (
            vsa_model(r).collapse().identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=20, upper_bound=55)))
        )

        # Subtraction
        r = r_2 - r_1
        assert isinstance(vsa_model(r), DiscreteStridedIntervalSet)
        assert (
            vsa_model(r).collapse().identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=35)))
        )


class TestSolution(unittest.TestCase):  # pylint: disable=no-member,function-redefined

    def setUp(self):
        self.solver_type = claripy.SolverVSA
        self.solver = self.solver_type()

    def test_solution_on_strided_interval(self):
        # Testing solution method with StridedInterval (SI) objects
        si = claripy.SI(bits=32, stride=10, lower_bound=32, upper_bound=320)
        assert self.solver.solution(si, si)
        assert self.solver.solution(si, 32)
        assert not self.solver.solution(si, 31)

        si2 = claripy.SI(bits=32, stride=0, lower_bound=3, upper_bound=3)
        assert self.solver.solution(si2, si2)
        assert self.solver.solution(si2, 3)
        assert not self.solver.solution(si2, 18)
        assert not self.solver.solution(si2, si)

    def test_solution_on_valueset(self):
        # Testing solution method with ValueSet (VS) objects
        vs = claripy.ValueSet(region="global", bits=32, value=0xDEADCA7)
        assert self.solver.solution(vs, 0xDEADCA7)
        assert not self.solver.solution(vs, 0xDEADBEEF)

    def test_solution_on_combined_valueset(self):
        # Testing solution method with a combination of ValueSet (VS) and StridedInterval (SI) objects
        si = claripy.SI(bits=32, stride=0, lower_bound=3, upper_bound=3)
        si2 = claripy.SI(bits=32, stride=10, lower_bound=32, upper_bound=320)

        vs = claripy.ValueSet(bits=si.size(), region="foo", value=claripy.backends.vsa.convert(si))
        vs2 = claripy.ValueSet(bits=si2.size(), region="foo", value=claripy.backends.vsa.convert(si2))
        vs = vs.union(vs2)

        assert self.solver.solution(vs, 3)
        assert self.solver.solution(vs, 122)
        assert self.solver.solution(vs, si)
        assert not self.solver.solution(vs, 2)
        assert not self.solver.solution(vs, 322)


class TestVSAReasonableBounds(unittest.TestCase):  # pylint: disable=no-member,function-redefined

    def setUp(self):
        self.backend = claripy.backends.vsa

    def test_reasonable_bounds_negative_only(self):
        # Testing reasonable bounds with only negative values
        si = claripy.SI(bits=32, stride=1, lower_bound=-20, upper_bound=-10)
        assert self.backend.max(si) == 0xFFFFFFF6
        assert self.backend.min(si) == 0xFFFFFFEC

    def test_reasonable_bounds_negative_and_positive(self):
        # Testing reasonable bounds with both negative and positive values
        si = claripy.SI(bits=32, stride=1, lower_bound=-20, upper_bound=10)
        assert self.backend.max(si) == 0xFFFFFFFF
        assert self.backend.min(si) == 0


class TestVSAShiftingOperations(unittest.TestCase):  # pylint: disable=no-member,function-redefined

    def setUp(self):
        self.identical = claripy.backends.vsa.identical

    def test_lshr_shift_by_1(self):
        # <32>1[2,4] LShR 1 = <32>1[1,2]
        si = claripy.SI(bits=32, stride=1, lower_bound=2, upper_bound=4)
        r = si.LShR(1)
        assert self.identical(r, claripy.SI(bits=32, stride=1, lower_bound=1, upper_bound=2))

    def test_lshr_shift_by_4(self):
        # <32>4[15,11] LShR 4 = <32>1[0, 0xfffffff]
        si = claripy.SI(bits=32, stride=4, lower_bound=15, upper_bound=11)
        r = si.LShR(4)
        assert self.identical(r, claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=0xFFFFFFF))

    def test_extract_operation(self):
        # Extract
        si = claripy.SI(bits=32, stride=4, lower_bound=15, upper_bound=11)
        r = si[31:4]
        assert self.identical(r, claripy.SI(bits=28, stride=1, lower_bound=0, upper_bound=0xFFFFFFF))

    def test_signed_shift_right(self):
        # <32>1[-4,-2] >> 1 = <32>1[-2,-1]
        si = claripy.SI(bits=32, stride=1, lower_bound=-4, upper_bound=-2)
        r = si >> 1
        assert self.identical(r, claripy.SI(bits=32, stride=1, lower_bound=-2, upper_bound=-1))

    def test_lshr_negative_shift(self):
        # <32>1[-4,-2] LShR 1 = <32>1[0x7ffffffe,0x7fffffff]
        si = claripy.SI(bits=32, stride=1, lower_bound=-4, upper_bound=-2)
        r = si.LShR(1)
        assert self.identical(r, claripy.SI(bits=32, stride=1, lower_bound=0x7FFFFFFE, upper_bound=0x7FFFFFFF))


class TestReverseOperations(unittest.TestCase):  # pylint: disable=no-member,function-redefined

    def setUp(self):
        self.backend = claripy.backends.vsa

    def test_reverse_and_intersection(self):
        # Reverse and intersection operations on StridedIntervals
        x = claripy.SI(name="TOP", bits=64, lower_bound=0, upper_bound=0xFFFFFFFFFFFFFFFF, stride=1)  # TOP
        y = claripy.SI(name="range", bits=64, lower_bound=0, upper_bound=1337, stride=1)  # [0, 1337]

        r0 = x.intersection(y)
        r1 = x.reversed.intersection(y)
        r2 = x.intersection(y.reversed).reversed
        r3 = x.reversed.intersection(y.reversed).reversed

        assert self.backend.convert(r0).max == 1337
        assert self.backend.convert(r1).max == 1337
        assert self.backend.convert(r2).max == 1337
        assert self.backend.convert(r3).max == 1337

    def test_reverse_discrete_strided_interval_set(self):
        # Reversing a DiscreteStridedIntervalSet
        # See claripy issue #95 for details.
        si0 = StridedInterval(name="a", bits=32, stride=0, lower_bound=0xFFFF0000, upper_bound=0xFFFF0000)
        si1 = StridedInterval(name="a", bits=32, stride=0, lower_bound=0xFFFF0001, upper_bound=0xFFFF0001)
        dsis = DiscreteStridedIntervalSet(name="b", bits=32, si_set={si0, si1})

        dsis_r = dsis.reverse()
        solver = claripy.SolverVSA()
        assert set(solver.eval(dsis_r, 3)) == {0xFFFF, 0x100FFFF}


if __name__ == "__main__":
    unittest.main()
