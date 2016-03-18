import claripy
import nose

from claripy.vsa import MaybeResult, BoolResult, DiscreteStridedIntervalSet, StridedInterval

def vsa_model(a):
    return claripy.backends.vsa.convert(a)

def test_fucked_extract():
    not_fucked = claripy.Reverse(claripy.Concat(claripy.BVS('file_/dev/stdin_6_0_16_8', 8, explicit_name=True), claripy.BVS('file_/dev/stdin_6_1_17_8', 8, explicit_name=True)))
    m = claripy.backends.vsa.max(not_fucked)
    assert m > 0

    zx = claripy.ZeroExt(16, not_fucked)
    pre_fucked = claripy.Reverse(zx)
    m = claripy.backends.vsa.max(pre_fucked)
    assert m > 0

    #print zx, claripy.backends.vsa.convert(zx)
    #print pre_fucked, claripy.backends.vsa.convert(pre_fucked)
    fucked = pre_fucked[31:16]
    m = claripy.backends.vsa.max(fucked)
    assert m > 0

    # here's another case
    wtf = (
        (
            claripy.Reverse(
                claripy.Concat(
                    claripy.BVS('w', 8), claripy.BVS('x', 8), claripy.BVS('y', 8), claripy.BVS('z', 8)
                )
            ) & claripy.BVV(15, 32)
        ) + claripy.BVV(48, 32)
    )[7:0]

    m = claripy.backends.vsa.max(wtf)
    assert m > 0

def test_reversed_concat():
    a = claripy.SI('a', 32, lower_bound=10, upper_bound=0x80, stride=10)
    b = claripy.SI('b', 32, lower_bound=1, upper_bound=0xff, stride=1)

    reversed_a = claripy.Reverse(a)
    reversed_b = claripy.Reverse(b)

    # First let's check if the reversing makes sense
    nose.tools.assert_equal(claripy.backends.vsa.min(reversed_a), 0xa000000)
    nose.tools.assert_equal(claripy.backends.vsa.max(reversed_a), 0x80000000)
    nose.tools.assert_equal(claripy.backends.vsa.min(reversed_b), 0x1000000)
    nose.tools.assert_equal(claripy.backends.vsa.max(reversed_b), 0xff000000)

    a_concat_b = claripy.Concat(a, b)
    nose.tools.assert_equal(a_concat_b._model_vsa._reversed, False)

    ra_concat_b = claripy.Concat(reversed_a, b)
    nose.tools.assert_equal(ra_concat_b._model_vsa._reversed, True)

    a_concat_rb = claripy.Concat(a, reversed_b)
    nose.tools.assert_equal(a_concat_rb._model_vsa._reversed, False)

    ra_concat_rb = claripy.Concat(reversed_a, reversed_b)
    nose.tools.assert_equal(ra_concat_rb._model_vsa._reversed, False)

def test_simple_cardinality():
    x = claripy.BVS('x', 32, 0xa, 0x14, 0xa)
    nose.tools.assert_equal(x.cardinality, 2)

def test_wrapped_intervals():
    #SI = claripy.StridedInterval

    # Disable the use of DiscreteStridedIntervalSet
    claripy.vsa.strided_interval.allow_dsis = False

    #
    # Signedness/unsignedness conversion
    #

    si1 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=0xffffffff)
    nose.tools.assert_equal(vsa_model(si1)._signed_bounds(), [ (0x0, 0x7fffffff), (-0x80000000, -0x1) ])
    nose.tools.assert_equal(vsa_model(si1)._unsigned_bounds(), [ (0x0, 0xffffffff) ])

    #
    # Pole-splitting
    #

    # south-pole splitting
    si1 = claripy.SI(bits=32, stride=1, lower_bound=-1, upper_bound=1)
    si_list = vsa_model(si1)._ssplit()
    nose.tools.assert_equal(len(si_list), 2)
    nose.tools.assert_true(
        si_list[0].identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=-1, upper_bound=-1))))
    nose.tools.assert_true(
        si_list[1].identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=1))))

    # north-pole splitting
    si1 = claripy.SI(bits=32, stride=1, lower_bound=-1, upper_bound=-3)
    si_list = vsa_model(si1)._nsplit()
    nose.tools.assert_equal(len(si_list), 2)
    nose.tools.assert_true(
        si_list[0].identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=-1, upper_bound=0x7fffffff))))
    nose.tools.assert_true(
        si_list[1].identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=0x80000000, upper_bound=-3))))

    # north-pole splitting, episode 2
    si1 = claripy.SI(bits=32, stride=3, lower_bound=3, upper_bound=0)
    si_list = vsa_model(si1)._nsplit()
    nose.tools.assert_equal(len(si_list), 2)
    nose.tools.assert_true(
        si_list[0].identical(vsa_model(claripy.SI(bits=32, stride=3, lower_bound=3, upper_bound=0x7ffffffe))))
    nose.tools.assert_true(
        si_list[1].identical(vsa_model(claripy.SI(bits=32, stride=3, lower_bound=0x80000001, upper_bound=0))))

    # bipolar splitting
    si1 = claripy.SI(bits=32, stride=1, lower_bound=-2, upper_bound=-8)
    si_list = vsa_model(si1)._psplit()
    nose.tools.assert_equal(len(si_list), 3)
    nose.tools.assert_true(
        si_list[0].identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=-2, upper_bound=-1))))
    nose.tools.assert_true(
        si_list[1].identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=0x7fffffff))))
    nose.tools.assert_true(
        si_list[2].identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=0x80000000, upper_bound=-8))))

    #
    # Addition
    #

    # Plain addition
    si1 = claripy.SI(bits=32, stride=1, lower_bound=-1, upper_bound=1)
    si2 = claripy.SI(bits=32, stride=1, lower_bound=-1, upper_bound=1)
    si3 = claripy.SI(bits=32, stride=1, lower_bound=-2, upper_bound=2)
    nose.tools.assert_true(claripy.backends.vsa.identical(si1 + si2, si3))
    si4 = claripy.SI(bits=32, stride=1, lower_bound=0xfffffffe, upper_bound=2)
    nose.tools.assert_true(claripy.backends.vsa.identical(si1 + si2, si4))
    si5 = claripy.SI(bits=32, stride=1, lower_bound=2, upper_bound=-2)
    nose.tools.assert_false(claripy.backends.vsa.identical(si1 + si2, si5))

    # Addition with overflowing cardinality
    si1 = claripy.SI(bits=8, stride=1, lower_bound=0, upper_bound=0xfe)
    si2 = claripy.SI(bits=8, stride=1, lower_bound=0xfe, upper_bound=0xff)
    nose.tools.assert_true(vsa_model((si1 + si2)).is_top)

    # Addition that shouldn't get a TOP
    si1 = claripy.SI(bits=8, stride=1, lower_bound=0, upper_bound=0xfe)
    si2 = claripy.SI(bits=8, stride=1, lower_bound=0, upper_bound=0)
    nose.tools.assert_false(vsa_model((si1 + si2)).is_top)

    #
    # Subtraction
    #

    si1 = claripy.SI(bits=8, stride=1, lower_bound=10, upper_bound=15)
    si2 = claripy.SI(bits=8, stride=1, lower_bound=11, upper_bound=12)
    si3 = claripy.SI(bits=8, stride=1, lower_bound=-2, upper_bound=4)
    nose.tools.assert_true(claripy.backends.vsa.identical(si1 - si2, si3))

    #
    # Multiplication
    #

    # integer multiplication
    si1 = claripy.SI(bits=32, to_conv=0xffff)
    si2 = claripy.SI(bits=32, to_conv=0x10000)
    si3 = claripy.SI(bits=32, to_conv=0xffff0000)
    nose.tools.assert_true(claripy.backends.vsa.identical(si1 * si2, si3))

    # intervals multiplication
    si1 = claripy.SI(bits=32, stride=1, lower_bound=10, upper_bound=15)
    si2 = claripy.SI(bits=32, stride=1, lower_bound=20, upper_bound=30)
    si3 = claripy.SI(bits=32, stride=1, lower_bound=200, upper_bound=450)
    nose.tools.assert_true(claripy.backends.vsa.identical(si1 * si2, si3))

    #
    # Division
    #

    # integer division
    si1 = claripy.SI(bits=32, to_conv=10)
    si2 = claripy.SI(bits=32, to_conv=5)
    si3 = claripy.SI(bits=32, to_conv=2)
    nose.tools.assert_true(claripy.backends.vsa.identical(si1 / si2, si3))

    si3 = claripy.SI(bits=32, to_conv=0)
    nose.tools.assert_true(claripy.backends.vsa.identical(si2 / si1, si3))

    # intervals division
    si1 = claripy.SI(bits=32, stride=1, lower_bound=10, upper_bound=100)
    si2 = claripy.SI(bits=32, stride=1, lower_bound=10, upper_bound=20)
    si3 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=10)
    nose.tools.assert_true(claripy.backends.vsa.identical(si1 / si2, si3))

    #
    # Extension
    #

    # zero-extension
    si1 = claripy.SI(bits=8, stride=1, lower_bound=0, upper_bound=0xfd)
    si_zext = si1.zero_extend(32 - 8)
    si_zext_ = claripy.SI(bits=32, stride=1, lower_bound=0x0, upper_bound=0xfd)
    nose.tools.assert_true(claripy.backends.vsa.identical(si_zext, si_zext_))

    # sign-extension
    si1 = claripy.SI(bits=8, stride=1, lower_bound=0, upper_bound=0xfd)
    si_sext = si1.sign_extend(32 - 8)
    si_sext_ = claripy.SI(bits=32, stride=1, lower_bound=0xffffff80, upper_bound=0x7f)
    nose.tools.assert_true(claripy.backends.vsa.identical(si_sext, si_sext_))

    #
    # Comparisons
    #

    # -1 == 0xff
    si1 = claripy.SI(bits=8, stride=1, lower_bound=-1, upper_bound=-1)
    si2 = claripy.SI(bits=8, stride=1, lower_bound=0xff, upper_bound=0xff)
    nose.tools.assert_true(claripy.backends.vsa.is_true(si1 == si2))

    # -2 != 0xff
    si1 = claripy.SI(bits=8, stride=1, lower_bound=-2, upper_bound=-2)
    si2 = claripy.SI(bits=8, stride=1, lower_bound=0xff, upper_bound=0xff)
    nose.tools.assert_true(claripy.backends.vsa.is_true(si1 != si2))

    # [-2, -1] < [1, 2] (signed arithmetic)
    si1 = claripy.SI(bits=8, stride=1, lower_bound=1, upper_bound=2)
    si2 = claripy.SI(bits=8, stride=1, lower_bound=-2, upper_bound=-1)
    nose.tools.assert_true(claripy.backends.vsa.is_true(si2.SLT(si1)))

    # [-2, -1] <= [1, 2] (signed arithmetic)
    nose.tools.assert_true(claripy.backends.vsa.is_true(si2.SLE(si1)))

    # [0xfe, 0xff] > [1, 2] (unsigned arithmetic)
    nose.tools.assert_true(claripy.backends.vsa.is_true(si2.UGT(si1)))

    # [0xfe, 0xff] >= [1, 2] (unsigned arithmetic)
    nose.tools.assert_true(claripy.backends.vsa.is_true(si2.UGE(si1)))

def test_join():
    # Set backend
    b = claripy.backends.vsa
    claripy.solver_backends = [ ]

    SI = claripy.SI

    a = claripy.SI(bits=8, to_conv=2)
    b = claripy.SI(bits=8, to_conv=10)
    c = claripy.SI(bits=8, to_conv=120)
    d = claripy.SI(bits=8, to_conv=130)
    e = claripy.SI(bits=8, to_conv=132)
    f = claripy.SI(bits=8, to_conv=135)

    # union a, b, c, d, e => [2, 132] with a stride of 2
    tmp1 = a.union(b)
    nose.tools.assert_true(claripy.backends.vsa.identical(tmp1, SI(bits=8, stride=8, lower_bound=2, upper_bound=10)))
    tmp2 = tmp1.union(c)
    nose.tools.assert_true(claripy.backends.vsa.identical(tmp2, SI(bits=8, stride=2, lower_bound=2, upper_bound=120)))
    tmp3 = tmp2.union(d).union(e)
    nose.tools.assert_true(claripy.backends.vsa.identical(tmp3, SI(bits=8, stride=2, lower_bound=2, upper_bound=132)))

    # union a, b, c, d, e, f => [2, 135] with a stride of 1
    tmp = a.union(b).union(c).union(d).union(e).union(f)
    nose.tools.assert_true(claripy.backends.vsa.identical(tmp, SI(bits=8, stride=1, lower_bound=2, upper_bound=135)))

    a = claripy.SI(bits=8, to_conv=1)
    b = claripy.SI(bits=8, to_conv=10)
    c = claripy.SI(bits=8, to_conv=120)
    d = claripy.SI(bits=8, to_conv=130)
    e = claripy.SI(bits=8, to_conv=132)
    f = claripy.SI(bits=8, to_conv=135)
    g = claripy.SI(bits=8, to_conv=220)
    h = claripy.SI(bits=8, to_conv=50)

    # union a, b, c, d, e, f, g, h => [220, 135] with a stride of 1
    tmp = a.union(b).union(c).union(d).union(e).union(f).union(g).union(h)
    nose.tools.assert_true(claripy.backends.vsa.identical(tmp, SI(bits=8, stride=1, lower_bound=220, upper_bound=135)))
    nose.tools.assert_true(220 in vsa_model(tmp).eval(255))
    nose.tools.assert_true(225 in vsa_model(tmp).eval(255))
    nose.tools.assert_true(0 in vsa_model(tmp).eval(255))
    nose.tools.assert_true(135 in vsa_model(tmp).eval(255))
    nose.tools.assert_false(138 in vsa_model(tmp).eval(255))

def test_vsa():
    # Set backend
    b = claripy.backends.vsa

    SI = claripy.SI
    VS = claripy.ValueSet
    BVV = claripy.BVV

    # Disable the use of DiscreteStridedIntervalSet
    claripy.vsa.strided_interval.allow_dsis = False

    def is_equal(ast_0, ast_1):
        return claripy.backends.vsa.identical(ast_0, ast_1)

    si1 = claripy.TSI(32, name="foo", explicit_name=True)
    nose.tools.assert_equal(vsa_model(si1).name, "foo")

    # Normalization
    si1 = SI(bits=32, stride=1, lower_bound=10, upper_bound=10)
    nose.tools.assert_equal(vsa_model(si1).stride, 0)

    # Integers
    si1 = claripy.SI(bits=32, stride=0, lower_bound=10, upper_bound=10)
    si2 = claripy.SI(bits=32, stride=0, lower_bound=10, upper_bound=10)
    si3 = claripy.SI(bits=32, stride=0, lower_bound=28, upper_bound=28)
    # Strided intervals
    si_a = claripy.SI(bits=32, stride=2, lower_bound=10, upper_bound=20)
    si_b = claripy.SI(bits=32, stride=2, lower_bound=-100, upper_bound=200)
    si_c = claripy.SI(bits=32, stride=3, lower_bound=-100, upper_bound=200)
    si_d = claripy.SI(bits=32, stride=2, lower_bound=50, upper_bound=60)
    si_e = claripy.SI(bits=16, stride=1, lower_bound=0x2000, upper_bound=0x3000)
    si_f = claripy.SI(bits=16, stride=1, lower_bound=0, upper_bound=255)
    si_g = claripy.SI(bits=16, stride=1, lower_bound=0, upper_bound=0xff)
    si_h = claripy.SI(bits=32, stride=0, lower_bound=0x80000000, upper_bound=0x80000000)

    nose.tools.assert_true(is_equal(si1, claripy.SI(bits=32, to_conv=10)))
    nose.tools.assert_true(is_equal(si2, claripy.SI(bits=32, to_conv=10)))
    nose.tools.assert_true(is_equal(si1, si2))
    # __add__
    si_add_1 = si1 + si2
    nose.tools.assert_true(is_equal(si_add_1, claripy.SI(bits=32, stride=0, lower_bound=20, upper_bound=20)))
    si_add_2 = si1 + si_a
    nose.tools.assert_true(is_equal(si_add_2, claripy.SI(bits=32, stride=2, lower_bound=20, upper_bound=30)))
    si_add_3 = si_a + si_b
    nose.tools.assert_true(is_equal(si_add_3, claripy.SI(bits=32, stride=2, lower_bound=-90, upper_bound=220)))
    si_add_4 = si_b + si_c
    nose.tools.assert_true(is_equal(si_add_4, claripy.SI(bits=32, stride=1, lower_bound=-200, upper_bound=400)))
    # __add__ with overflow
    si_add_5 = si_h + 0xffffffff
    nose.tools.assert_true(is_equal(si_add_5, claripy.SI(bits=32, stride=0, lower_bound=0x7fffffff, upper_bound=0x7fffffff)))
    # __sub__
    si_minus_1 = si1 - si2
    nose.tools.assert_true(is_equal(si_minus_1, claripy.SI(bits=32, stride=0, lower_bound=0, upper_bound=0)))
    si_minus_2 = si_a - si_b
    nose.tools.assert_true(is_equal(si_minus_2, claripy.SI(bits=32, stride=2, lower_bound=-190, upper_bound=120)))
    si_minus_3 = si_b - si_c
    nose.tools.assert_true(is_equal(si_minus_3, claripy.SI(bits=32, stride=1, lower_bound=-300, upper_bound=300)))
    # __neg__ / __invert__ / bitwise not
    si_neg_1 = ~si1
    nose.tools.assert_true(is_equal(si_neg_1, claripy.SI(bits=32, to_conv=-11)))
    si_neg_2 = ~si_b
    nose.tools.assert_true(is_equal(si_neg_2, claripy.SI(bits=32, stride=2, lower_bound=-201, upper_bound=99)))
    # __or__
    si_or_1 = si1 | si3
    nose.tools.assert_true(is_equal(si_or_1, claripy.SI(bits=32, to_conv=30)))
    si_or_2 = si1 | si2
    nose.tools.assert_true(is_equal(si_or_2, claripy.SI(bits=32, to_conv=10)))
    si_or_3 = si1 | si_a # An integer | a strided interval
    nose.tools.assert_true(is_equal(si_or_3 , claripy.SI(bits=32, stride=2, lower_bound=10, upper_bound=30)))
    si_or_3 = si_a | si1 # Exchange the operands
    nose.tools.assert_true(is_equal(si_or_3, claripy.SI(bits=32, stride=2, lower_bound=10, upper_bound=30)))
    si_or_4 = si_a | si_d # A strided interval | another strided interval
    nose.tools.assert_true(is_equal(si_or_4, claripy.SI(bits=32, stride=2, lower_bound=50, upper_bound=62)))
    si_or_4 = si_d | si_a # Exchange the operands
    nose.tools.assert_true(is_equal(si_or_4, claripy.SI(bits=32, stride=2, lower_bound=50, upper_bound=62)))
    si_or_5 = si_e | si_f #
    nose.tools.assert_true(is_equal(si_or_5, claripy.SI(bits=16, stride=1, lower_bound=0x2000, upper_bound=0x30ff)))
    si_or_6 = si_e | si_g #
    nose.tools.assert_true(is_equal(si_or_6, claripy.SI(bits=16, stride=1, lower_bound=0x2000, upper_bound=0x30ff)))
    # Shifting
    si_shl_1 = si1 << 3
    nose.tools.assert_equal(si_shl_1.size(), 32)
    nose.tools.assert_true(is_equal(si_shl_1, claripy.SI(bits=32, stride=0, lower_bound=80, upper_bound=80)))
    # Multiplication
    si_mul_1 = si1 * 3
    nose.tools.assert_equal(si_mul_1.size(), 32)
    nose.tools.assert_true(is_equal(si_mul_1, claripy.SI(bits=32, stride=0, lower_bound=30, upper_bound=30)))
    si_mul_2 = si_a * 3
    nose.tools.assert_equal(si_mul_2.size(), 32)
    nose.tools.assert_true(is_equal(si_mul_2, claripy.SI(bits=32, stride=6, lower_bound=30, upper_bound=60)))
    si_mul_3 = si_a * si_b
    nose.tools.assert_equal(si_mul_3.size(), 32)
    nose.tools.assert_true(is_equal(si_mul_3, claripy.SI(bits=32, stride=2, lower_bound=-2000, upper_bound=4000)))
    # Division
    si_div_1 = si1 / 3
    nose.tools.assert_equal(si_div_1.size(), 32)
    nose.tools.assert_true(is_equal(si_div_1, claripy.SI(bits=32, stride=0, lower_bound=3, upper_bound=3)))
    si_div_2 = si_a / 3
    nose.tools.assert_equal(si_div_2.size(), 32)
    nose.tools.assert_true(is_equal(si_div_2, claripy.SI(bits=32, stride=1, lower_bound=3, upper_bound=6)))
    # Modulo
    si_mo_1 = si1 % 3
    nose.tools.assert_equal(si_mo_1.size(), 32)
    nose.tools.assert_true(is_equal(si_mo_1, claripy.SI(bits=32, stride=0, lower_bound=1, upper_bound=1)))
    si_mo_2 = si_a % 3
    nose.tools.assert_equal(si_mo_2.size(), 32)
    nose.tools.assert_true(is_equal(si_mo_2, claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=2)))

    #
    # Extracting the sign bit
    #

    # a negative integer
    si = claripy.SI(bits=64, stride=0, lower_bound=-1, upper_bound=-1)
    sb = si[63: 63]
    nose.tools.assert_true(is_equal(sb, claripy.SI(bits=1, to_conv=1)))

    # non-positive integers
    si = claripy.SI(bits=64, stride=1, lower_bound=-1, upper_bound=0)
    sb = si[63: 63]
    nose.tools.assert_true(is_equal(sb, claripy.SI(bits=1, stride=1, lower_bound=0, upper_bound=1)))

    # Extracting an integer
    si = claripy.SI(bits=64, stride=0, lower_bound=0x7fffffffffff0000, upper_bound=0x7fffffffffff0000)
    part1 = si[63 : 32]
    part2 = si[31 : 0]
    nose.tools.assert_true(is_equal(part1, claripy.SI(bits=32, stride=0, lower_bound=0x7fffffff, upper_bound=0x7fffffff)))
    nose.tools.assert_true(is_equal(part2, claripy.SI(bits=32, stride=0, lower_bound=0xffff0000, upper_bound=0xffff0000)))

    # Concatenating two integers
    si_concat = part1.concat(part2)
    nose.tools.assert_true(is_equal(si_concat, si))

    # Extracting a claripy.SI
    si = claripy.SI(bits=64, stride=0x9, lower_bound=0x1, upper_bound=0xa)
    part1 = si[63 : 32]
    part2 = si[31 : 0]
    nose.tools.assert_true(is_equal(part1, claripy.SI(bits=32, stride=0, lower_bound=0x0, upper_bound=0x0)))
    nose.tools.assert_true(is_equal(part2, claripy.SI(bits=32, stride=9, lower_bound=1, upper_bound=10)))

    # Concatenating two claripy.SIs
    si_concat = part1.concat(part2)
    nose.tools.assert_true(is_equal(si_concat, si))

    # Concatenating two SIs that are of different sizes
    si_1 = SI(bits=64, stride=1, lower_bound=0, upper_bound=0xffffffffffffffff)
    si_2 = SI(bits=32, stride=1, lower_bound=0, upper_bound=0xffffffff)
    si_concat = si_1.concat(si_2)
    nose.tools.assert_true(is_equal(si_concat, SI(bits=96, stride=1,
                                                  lower_bound=0,
                                                  upper_bound=0xffffffffffffffffffffffff)))

    # Zero-Extend the low part
    si_zeroextended = part2.zero_extend(32)
    nose.tools.assert_true(is_equal(si_zeroextended, claripy.SI(bits=64, stride=9, lower_bound=1, upper_bound=10)))

    # Sign-extension
    si_signextended = part2.sign_extend(32)
    nose.tools.assert_true(is_equal(si_signextended, claripy.SI(bits=64, stride=9, lower_bound=1, upper_bound=10)))

    # Extract from the result above
    si_extracted = si_zeroextended[31:0]
    nose.tools.assert_true(is_equal(si_extracted, claripy.SI(bits=32, stride=9, lower_bound=1, upper_bound=10)))

    # Union
    si_union_1 = si1.union(si2)
    nose.tools.assert_true(is_equal(si_union_1, claripy.SI(bits=32, stride=0, lower_bound=10, upper_bound=10)))
    si_union_2 = si1.union(si3)
    nose.tools.assert_true(is_equal(si_union_2, claripy.SI(bits=32, stride=18, lower_bound=10, upper_bound=28)))
    si_union_3 = si1.union(si_a)
    nose.tools.assert_true(is_equal(si_union_3, claripy.SI(bits=32, stride=2, lower_bound=10, upper_bound=20)))
    si_union_4 = si_a.union(si_b)
    nose.tools.assert_true(is_equal(si_union_4, claripy.SI(bits=32, stride=2, lower_bound=-100, upper_bound=200)))
    si_union_5 = si_b.union(si_c)
    nose.tools.assert_true(is_equal(si_union_5, claripy.SI(bits=32, stride=1, lower_bound=-100, upper_bound=200)))

    # Intersection
    si_intersection_1 = si1.intersection(si1)
    nose.tools.assert_true(is_equal(si_intersection_1, si2))
    si_intersection_2 = si1.intersection(si2)
    nose.tools.assert_true(is_equal(si_intersection_2, claripy.SI(bits=32, stride=0, lower_bound=10, upper_bound=10)))
    si_intersection_3 = si1.intersection(si_a)
    nose.tools.assert_true(is_equal(si_intersection_3, claripy.SI(bits=32, stride=0, lower_bound=10, upper_bound=10)))

    si_intersection_4 = si_a.intersection(si_b)

    nose.tools.assert_true(is_equal(si_intersection_4, claripy.SI(bits=32, stride=2, lower_bound=10, upper_bound=20)))
    si_intersection_5 = si_b.intersection(si_c)
    nose.tools.assert_true(is_equal(si_intersection_5, claripy.SI(bits=32, stride=6, lower_bound=-100, upper_bound=200)))

    # More intersections
    t0 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=0x27)
    t1 = claripy.SI(bits=32, stride=0x7fffffff, lower_bound=0x80000002, upper_bound=1)

    si_is_6 = t0.intersection(t1)
    nose.tools.assert_true(is_equal(si_is_6, claripy.SI(bits=32, stride=0, lower_bound=1, upper_bound=1)))

    t2 = claripy.SI(bits=32, stride=5, lower_bound=20, upper_bound=30)
    t3 = claripy.SI(bits=32, stride=1, lower_bound=27, upper_bound=0xffffffff)

    si_is_7 = t2.intersection(t3)
    nose.tools.assert_true(is_equal(si_is_7, claripy.SI(bits=32, stride=0, lower_bound=30, upper_bound=30)))

    t4 = claripy.SI(bits=32, stride=5, lower_bound=-400, upper_bound=400)
    t5 = claripy.SI(bits=32, stride=1, lower_bound=395, upper_bound=-395)
    si_is_8 = t4.intersection(t5)
    nose.tools.assert_true(is_equal(si_is_8, claripy.SI(bits=32, stride=5, lower_bound=-400, upper_bound=400)))

    # Sign-extension
    si = claripy.SI(bits=1, stride=0, lower_bound=1, upper_bound=1)
    si_signextended = si.sign_extend(31)
    nose.tools.assert_true(is_equal(si_signextended, claripy.SI(bits=32, stride=0, lower_bound=0xffffffff, upper_bound=0xffffffff)))

    # Comparison between claripy.SI and BVV
    si = claripy.SI(bits=32, stride=1, lower_bound=-0x7f, upper_bound=0x7f)
    si._model_vsa.uninitialized = True
    bvv = BVV(0x30, 32)
    comp = (si < bvv)
    nose.tools.assert_true(vsa_model(comp).identical(MaybeResult()))

    # Better extraction
    # si = <32>0x1000000[0xcffffff, 0xdffffff]R
    si = claripy.SI(bits=32, stride=0x1000000, lower_bound=0xcffffff, upper_bound=0xdffffff)
    si_byte0 = si[7: 0]
    si_byte1 = si[15: 8]
    si_byte2 = si[23: 16]
    si_byte3 = si[31: 24]
    nose.tools.assert_true(is_equal(si_byte0, claripy.SI(bits=8, stride=0, lower_bound=0xff, upper_bound=0xff)))
    nose.tools.assert_true(is_equal(si_byte1, claripy.SI(bits=8, stride=0, lower_bound=0xff, upper_bound=0xff)))
    nose.tools.assert_true(is_equal(si_byte2, claripy.SI(bits=8, stride=0, lower_bound=0xff, upper_bound=0xff)))
    nose.tools.assert_true(is_equal(si_byte3, claripy.SI(bits=8, stride=1, lower_bound=0xc, upper_bound=0xd)))

    # Optimization on bitwise-and
    si_1 = claripy.SI(bits=32, stride=1, lower_bound=0x0, upper_bound=0xffffffff)
    si_2 = claripy.SI(bits=32, stride=0, lower_bound=0x80000000, upper_bound=0x80000000)
    si = si_1 & si_2
    nose.tools.assert_true(is_equal(si, claripy.SI(bits=32, stride=0x80000000, lower_bound=0, upper_bound=0x80000000)))

    si_1 = claripy.SI(bits=32, stride=1, lower_bound=0x0, upper_bound=0x7fffffff)
    si_2 = claripy.SI(bits=32, stride=0, lower_bound=0x80000000, upper_bound=0x80000000)
    si = si_1 & si_2
    nose.tools.assert_true(is_equal(si, claripy.SI(bits=32, stride=0, lower_bound=0, upper_bound=0)))

    # Concatenation: concat with zeros only increases the stride
    si_1 = claripy.SI(bits=8, stride=0xff, lower_bound=0x0, upper_bound=0xff)
    si_2 = claripy.SI(bits=8, stride=0, lower_bound=0, upper_bound=0)
    si = si_1.concat(si_2)
    nose.tools.assert_true(is_equal(si, claripy.SI(bits=16, stride=0xff00, lower_bound=0, upper_bound=0xff00)))

    # Extract from a reversed value
    si_1 = claripy.SI(bits=64, stride=0xff, lower_bound=0x0, upper_bound=0xff)
    si_2 = si_1.reversed[63 : 56]
    nose.tools.assert_true(is_equal(si_2, claripy.SI(bits=8, stride=0xff, lower_bound=0x0, upper_bound=0xff)))

    #
    # ValueSet
    #

    vs_1 = claripy.ValueSet(bits=32)
    nose.tools.assert_true(vsa_model(vs_1).is_empty, True)
    # Test merging two addresses
    vsa_model(vs_1).merge_si('global', vsa_model(si1))
    vsa_model(vs_1).merge_si('global', vsa_model(si3))
    nose.tools.assert_true(vsa_model(vs_1).get_si('global').identical(vsa_model(SI(bits=32, stride=18, lower_bound=10, upper_bound=28))))
    # Length of this ValueSet
    nose.tools.assert_equal(len(vsa_model(vs_1)), 32)

    vs_1 = claripy.ValueSet(name='boo', bits=32)
    vs_2 = claripy.ValueSet(name='foo', bits=32)
    nose.tools.assert_true(claripy.backends.vsa.identical(vs_1, vs_1))
    nose.tools.assert_true(claripy.backends.vsa.identical(vs_2, vs_2))
    vsa_model(vs_1).merge_si('global', vsa_model(si1))
    nose.tools.assert_false(claripy.backends.vsa.identical(vs_1, vs_2))
    vsa_model(vs_2).merge_si('global', vsa_model(si1))
    nose.tools.assert_true(claripy.backends.vsa.identical(vs_1, vs_2))
    nose.tools.assert_true(claripy.backends.vsa.is_true((vs_1 & vs_2) == vs_1))
    vsa_model(vs_1).merge_si('global', vsa_model(si3))
    nose.tools.assert_false(claripy.backends.vsa.identical(vs_1, vs_2))

    # Subtraction
    # Subtraction of two pointers yields a concrete value

    vs_1 = claripy.ValueSet(name='foo', region='global', bits=32, val=0x400010)
    vs_2 = claripy.ValueSet(name='bar', region='global', bits=32, val=0x400000)
    si = vs_1 - vs_2
    nose.tools.assert_is(type(vsa_model(si)), StridedInterval)
    nose.tools.assert_true(claripy.backends.vsa.identical(si, claripy.SI(bits=32, stride=0, lower_bound=0x10, upper_bound=0x10)))

    #
    # IfProxy
    #

    si = claripy.SI(bits=32, stride=1, lower_bound=10, upper_bound=0xffffffff)
    if_0 = claripy.If(si == 0, si, si - 1)
    nose.tools.assert_true(claripy.backends.vsa.identical(if_0, if_0))
    nose.tools.assert_false(claripy.backends.vsa.identical(if_0, si))

    # max and min on IfProxy
    si = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=0xffffffff)
    if_0 = claripy.If(si == 0, si, si - 1)
    max_val = b.max(if_0)
    min_val = b.min(if_0)
    nose.tools.assert_equal(max_val, 0xffffffff)
    nose.tools.assert_equal(min_val, 0x00000000)

    # identical
    nose.tools.assert_true(claripy.backends.vsa.identical(if_0, if_0))
    nose.tools.assert_true(claripy.backends.vsa.identical(if_0, si))
    if_0_copy = claripy.If(si == 0, si, si - 1)
    nose.tools.assert_true(claripy.backends.vsa.identical(if_0, if_0_copy))
    if_1 = claripy.If(si == 1, si, si - 1)
    nose.tools.assert_true(claripy.backends.vsa.identical(if_0, if_1))

    si = SI(bits=32, stride=0, lower_bound=1, upper_bound=1)
    if_0 = claripy.If(si == 0, si, si - 1)
    if_0_copy = claripy.If(si == 0, si, si - 1)
    nose.tools.assert_true(claripy.backends.vsa.identical(if_0, if_0_copy))
    if_1 = claripy.If(si == 1, si, si - 1)
    nose.tools.assert_false(claripy.backends.vsa.identical(if_0, if_1))
    if_1 = claripy.If(si == 0, si + 1, si - 1)
    nose.tools.assert_true(claripy.backends.vsa.identical(if_0, if_1))
    if_1 = claripy.If(si == 0, si, si)
    nose.tools.assert_false(claripy.backends.vsa.identical(if_0, if_1))

    # if_1 = And(VS_2, IfProxy(si == 0, 0, 1))
    vs_2 = VS(region='global', bits=32, val=0xFA7B00B)
    si = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=1)
    if_1 = (vs_2 & claripy.If(si == 0, claripy.SI(bits=32, stride=0, lower_bound=0, upper_bound=0), claripy.SI(bits=32, stride=0, lower_bound=0xffffffff, upper_bound=0xffffffff)))
    nose.tools.assert_true(claripy.backends.vsa.is_true(vsa_model(if_1.ite_excavated.args[1]) == vsa_model(VS(region='global', bits=32, val=0))))
    nose.tools.assert_true(claripy.backends.vsa.is_true(vsa_model(if_1.ite_excavated.args[2]) == vsa_model(vs_2)))

    # if_2 = And(VS_3, IfProxy(si != 0, 0, 1)
    vs_3 = claripy.ValueSet(region='global', bits=32, val=0xDEADCA7)
    si = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=1)
    if_2 = (vs_3 & claripy.If(si != 0, claripy.SI(bits=32, stride=0, lower_bound=0, upper_bound=0), claripy.SI(bits=32, stride=0, lower_bound=0xffffffff, upper_bound=0xffffffff)))
    nose.tools.assert_true(claripy.backends.vsa.is_true(vsa_model(if_2.ite_excavated.args[1]) == vsa_model(VS(region='global', bits=32, val=0))))
    nose.tools.assert_true(claripy.backends.vsa.is_true(vsa_model(if_2.ite_excavated.args[2]) == vsa_model(vs_3)))

    # Something crazy is gonna happen...
    #if_3 = if_1 + if_2
    #nose.tools.assert_true(claripy.backends.vsa.is_true(vsa_model(if_3.ite_excavated.args[1]) == vsa_model(vs_3)))
    #nose.tools.assert_true(claripy.backends.vsa.is_true(vsa_model(if_3.ite_excavated.args[1]) == vsa_model(vs_2)))

def test_vsa_constraint_to_si():
    # Set backend
    b = claripy.backends.vsa
    s = claripy.LightFrontend(claripy.backends.vsa) #pylint:disable=unused-variable

    SI = claripy.SI
    BVV = claripy.BVV

    claripy.vsa.strided_interval.allow_dsis = False

    #
    # If(SI == 0, 1, 0) == 1
    #

    s1 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=2)
    ast_true = (claripy.If(s1 == BVV(0, 32), BVV(1, 1), BVV(0, 1)) == BVV(1, 1))
    ast_false = (claripy.If(s1 == BVV(0, 32), BVV(1, 1), BVV(0, 1)) != BVV(1, 1))

    trueside_sat, trueside_replacement = b.constraint_to_si(ast_true)
    nose.tools.assert_equal(trueside_sat, True)
    nose.tools.assert_equal(len(trueside_replacement), 1)
    nose.tools.assert_true(trueside_replacement[0][0] is s1)
    # True side: claripy.SI<32>0[0, 0]
    nose.tools.assert_true(
        claripy.backends.vsa.is_true(trueside_replacement[0][1] == claripy.SI(bits=32, stride=0, lower_bound=0, upper_bound=0)))

    falseside_sat, falseside_replacement = b.constraint_to_si(ast_false)
    nose.tools.assert_equal(falseside_sat, True)
    nose.tools.assert_equal(len(falseside_replacement), 1)
    nose.tools.assert_true(falseside_replacement[0][0] is s1)
    # False side; claripy.SI<32>1[1, 2]

    nose.tools.assert_true(
        claripy.backends.vsa.identical(falseside_replacement[0][1], SI(bits=32, stride=1, lower_bound=1, upper_bound=2))
    )

    #
    # If(SI == 0, 1, 0) <= 1
    #

    s1 = SI(bits=32, stride=1, lower_bound=0, upper_bound=2)
    ast_true = (claripy.If(s1 == BVV(0, 32), BVV(1, 1), BVV(0, 1)) <= BVV(1, 1))
    ast_false = (claripy.If(s1 == BVV(0, 32), BVV(1, 1), BVV(0, 1)) > BVV(1, 1))

    trueside_sat, trueside_replacement = b.constraint_to_si(ast_true)
    nose.tools.assert_equal(trueside_sat, True) # Always satisfiable

    falseside_sat, falseside_replacement = b.constraint_to_si(ast_false)
    nose.tools.assert_equal(falseside_sat, False) # Not sat

    #
    # If(SI == 0, 20, 10) > 15
    #

    s1 = SI(bits=32, stride=1, lower_bound=0, upper_bound=2)
    ast_true = (claripy.If(s1 == BVV(0, 32), BVV(20, 32), BVV(10, 32)) > BVV(15, 32))
    ast_false = (claripy.If(s1 == BVV(0, 32), BVV(20, 32), BVV(10, 32)) <= BVV(15, 32))

    trueside_sat, trueside_replacement = b.constraint_to_si(ast_true)
    nose.tools.assert_equal(trueside_sat, True)
    nose.tools.assert_equal(len(trueside_replacement), 1)
    nose.tools.assert_true(trueside_replacement[0][0] is s1)
    # True side: SI<32>0[0, 0]
    nose.tools.assert_true(
        claripy.backends.vsa.identical(trueside_replacement[0][1], SI(bits=32, stride=0, lower_bound=0, upper_bound=0))
    )

    falseside_sat, falseside_replacement = b.constraint_to_si(ast_false)
    nose.tools.assert_equal(falseside_sat, True)
    nose.tools.assert_equal(len(falseside_replacement), 1)
    nose.tools.assert_true(falseside_replacement[0][0] is s1)
    # False side; SI<32>1[1, 2]
    nose.tools.assert_true(
        claripy.backends.vsa.identical(falseside_replacement[0][1], SI(bits=32, stride=1, lower_bound=1, upper_bound=2))
    )

    #
    # If(SI == 0, 20, 10) >= 15
    #

    s1 = SI(bits=32, stride=1, lower_bound=0, upper_bound=2)
    ast_true = (claripy.If(s1 == BVV(0, 32), BVV(15, 32), BVV(10, 32)) >= BVV(15, 32))
    ast_false = (claripy.If(s1 == BVV(0, 32), BVV(15, 32), BVV(10, 32)) < BVV(15, 32))

    trueside_sat, trueside_replacement = b.constraint_to_si(ast_true)
    nose.tools.assert_equal(trueside_sat, True)
    nose.tools.assert_equal(len(trueside_replacement), 1)
    nose.tools.assert_true(trueside_replacement[0][0] is s1)
    # True side: SI<32>0[0, 0]
    nose.tools.assert_true(
        claripy.backends.vsa.identical(trueside_replacement[0][1], SI(bits=32, stride=0, lower_bound=0, upper_bound=0))
    )

    falseside_sat, falseside_replacement = b.constraint_to_si(ast_false)
    nose.tools.assert_equal(falseside_sat, True)
    nose.tools.assert_equal(len(falseside_replacement), 1)
    nose.tools.assert_true(falseside_replacement[0][0] is s1)
    # False side; SI<32>0[0,0]
    nose.tools.assert_true(
        claripy.backends.vsa.identical(falseside_replacement[0][1], SI(bits=32, stride=1, lower_bound=1, upper_bound=2))
    )

    #
    # Extract(0, 0, Concat(BVV(0, 63), If(SI == 0, 1, 0))) == 1
    #

    s2 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=2)
    ast_true = (claripy.Extract(0, 0, claripy.Concat(BVV(0, 63), claripy.If(s2 == 0, BVV(1, 1), BVV(0, 1)))) == 1)
    ast_false = (claripy.Extract(0, 0, claripy.Concat(BVV(0, 63), claripy.If(s2 == 0, BVV(1, 1), BVV(0, 1)))) != 1)

    trueside_sat, trueside_replacement = b.constraint_to_si(ast_true)
    nose.tools.assert_equal(trueside_sat, True)
    nose.tools.assert_equal(len(trueside_replacement), 1)
    nose.tools.assert_true(trueside_replacement[0][0] is s2)
    # True side: claripy.SI<32>0[0, 0]
    nose.tools.assert_true(
        claripy.backends.vsa.identical(trueside_replacement[0][1], SI(bits=32, stride=0, lower_bound=0, upper_bound=0))
    )

    falseside_sat, falseside_replacement = b.constraint_to_si(ast_false)
    nose.tools.assert_equal(falseside_sat, True)
    nose.tools.assert_equal(len(falseside_replacement), 1)
    nose.tools.assert_true(falseside_replacement[0][0] is s2)
    # False side; claripy.SI<32>1[1, 2]
    nose.tools.assert_true(
        claripy.backends.vsa.identical(falseside_replacement[0][1], SI(bits=32, stride=1, lower_bound=1, upper_bound=2))
    )

    #
    # Extract(0, 0, ZeroExt(32, If(SI == 0, BVV(1, 32), BVV(0, 32)))) == 1
    #

    s3 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=2)
    ast_true = (claripy.Extract(0, 0, claripy.ZeroExt(32, claripy.If(s3 == 0, BVV(1, 32), BVV(0, 32)))) == 1)
    ast_false = (claripy.Extract(0, 0, claripy.ZeroExt(32, claripy.If(s3 == 0, BVV(1, 32), BVV(0, 32)))) != 1)

    trueside_sat, trueside_replacement = b.constraint_to_si(ast_true)
    nose.tools.assert_equal(trueside_sat, True)
    nose.tools.assert_equal(len(trueside_replacement), 1)
    nose.tools.assert_true(trueside_replacement[0][0] is s3)
    # True side: claripy.SI<32>0[0, 0]
    nose.tools.assert_true(
        claripy.backends.vsa.identical(trueside_replacement[0][1], SI(bits=32, stride=0, lower_bound=0, upper_bound=0))
    )

    falseside_sat, falseside_replacement = b.constraint_to_si(ast_false)
    nose.tools.assert_equal(falseside_sat, True)
    nose.tools.assert_equal(len(falseside_replacement), 1)
    nose.tools.assert_true(falseside_replacement[0][0] is s3)
    # False side; claripy.SI<32>1[1, 2]
    nose.tools.assert_true(
        claripy.backends.vsa.identical(falseside_replacement[0][1], SI(bits=32, stride=1, lower_bound=1, upper_bound=2))
    )

    #
    # Extract(0, 0, ZeroExt(32, If(Extract(32, 0, (SI & claripy.SI)) < 0, BVV(1, 1), BVV(0, 1))))
    #

    s4 = claripy.SI(bits=64, stride=1, lower_bound=0, upper_bound=0xffffffffffffffff)
    ast_true = (
        claripy.Extract(0, 0, claripy.ZeroExt(32, claripy.If(claripy.Extract(31, 0, (s4 & s4)).SLT(0), BVV(1, 32), BVV(0, 32)))) == 1)
    ast_false = (
        claripy.Extract(0, 0, claripy.ZeroExt(32, claripy.If(claripy.Extract(31, 0, (s4 & s4)).SLT(0), BVV(1, 32), BVV(0, 32)))) != 1)

    trueside_sat, trueside_replacement = b.constraint_to_si(ast_true)
    nose.tools.assert_equal(trueside_sat, True)
    nose.tools.assert_equal(len(trueside_replacement), 1)
    nose.tools.assert_true(trueside_replacement[0][0] is s4[31:0])
    # True side: claripy.SI<32>0[0, 0]
    nose.tools.assert_true(
        claripy.backends.vsa.identical(trueside_replacement[0][1], SI(bits=32, stride=1, lower_bound=-0x80000000, upper_bound=-1))
    )

    falseside_sat, falseside_replacement = b.constraint_to_si(ast_false)
    nose.tools.assert_equal(falseside_sat, True)
    nose.tools.assert_equal(len(falseside_replacement), 1)
    nose.tools.assert_true(falseside_replacement[0][0] is s4[31:0])
    # False side; claripy.SI<32>1[1, 2]
    nose.tools.assert_true(
        claripy.backends.vsa.identical(falseside_replacement[0][1], SI(bits=32, stride=1, lower_bound=0, upper_bound=0x7fffffff))
    )

    # TODO: Add some more insane test cases

def test_vsa_discrete_value_set():
    """
    Test cases for DiscreteStridedIntervalSet.
    """
    # Set backend
    b = claripy.backends.vsa

    s = claripy.LightFrontend(claripy.backends.vsa) #pylint:disable=unused-variable

    SI = claripy.SI
    BVV = claripy.BVV

    # Allow the use of DiscreteStridedIntervalSet (cuz we wanna test it!)
    claripy.vsa.strided_interval.allow_dsis = True

    #
    # Union
    #
    val_1 = BVV(0, 32)
    val_2 = BVV(1, 32)
    r = val_1.union(val_2)
    nose.tools.assert_true(isinstance(vsa_model(r), DiscreteStridedIntervalSet))
    nose.tools.assert_true(vsa_model(r).collapse(), claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=1))

    r = r.union(BVV(3, 32))
    ints = b.eval(r, 4)
    nose.tools.assert_equal(len(ints), 3)
    nose.tools.assert_equal(ints, [0, 1, 3])

    #
    # Intersection
    #

    val_1 = BVV(0, 32)
    val_2 = BVV(1, 32)
    r = val_1.intersection(val_2)
    nose.tools.assert_true(isinstance(vsa_model(r), StridedInterval))
    nose.tools.assert_true(vsa_model(r).is_empty)

    val_1 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=10)
    val_2 = claripy.SI(bits=32, stride=1, lower_bound=10, upper_bound=20)
    val_3 = claripy.SI(bits=32, stride=1, lower_bound=15, upper_bound=50)
    r = val_1.union(val_2)
    nose.tools.assert_true(isinstance(vsa_model(r), DiscreteStridedIntervalSet))
    r = r.intersection(val_3)
    nose.tools.assert_equal(sorted(b.eval(r, 100)), [ 15, 16, 17, 18, 19, 20 ])

    #
    # Some logical operations
    #

    val_1 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=10)
    val_2 = claripy.SI(bits=32, stride=1, lower_bound=5, upper_bound=20)
    r_1 = val_1.union(val_2)
    val_3 = claripy.SI(bits=32, stride=1, lower_bound=20, upper_bound=30)
    val_4 = claripy.SI(bits=32, stride=1, lower_bound=25, upper_bound=35)
    r_2 = val_3.union(val_4)
    nose.tools.assert_true(isinstance(vsa_model(r_1), DiscreteStridedIntervalSet))
    nose.tools.assert_true(isinstance(vsa_model(r_2), DiscreteStridedIntervalSet))
    # r_1 < r_2
    nose.tools.assert_true(BoolResult.is_maybe(vsa_model(r_1 < r_2)))
    # r_1 <= r_2
    nose.tools.assert_true(BoolResult.is_true(vsa_model(r_1 <= r_2)))
    # r_1 >= r_2
    nose.tools.assert_true(BoolResult.is_maybe(vsa_model(r_1 >= r_2)))
    # r_1 > r_2
    nose.tools.assert_true(BoolResult.is_false(vsa_model(r_1 > r_2)))
    # r_1 == r_2
    nose.tools.assert_true(BoolResult.is_maybe(vsa_model(r_1 == r_2)))
    # r_1 != r_2
    nose.tools.assert_true(BoolResult.is_maybe(vsa_model(r_1 != r_2)))

    #
    # Some arithmetic operations
    #

    val_1 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=10)
    val_2 = claripy.SI(bits=32, stride=1, lower_bound=5, upper_bound=20)
    r_1 = val_1.union(val_2)
    val_3 = claripy.SI(bits=32, stride=1, lower_bound=20, upper_bound=30)
    val_4 = claripy.SI(bits=32, stride=1, lower_bound=25, upper_bound=35)
    r_2 = val_3.union(val_4)
    nose.tools.assert_true(isinstance(vsa_model(r_1), DiscreteStridedIntervalSet))
    nose.tools.assert_true(isinstance(vsa_model(r_2), DiscreteStridedIntervalSet))
    # r_1 + r_2
    r = r_1 + r_2
    nose.tools.assert_true(isinstance(vsa_model(r), DiscreteStridedIntervalSet))
    nose.tools.assert_true(vsa_model(r).collapse().identical(vsa_model(SI(bits=32, stride=1, lower_bound=20, upper_bound=55))))
    # r_2 - r_1
    r = r_2 - r_1
    nose.tools.assert_true(isinstance(vsa_model(r), DiscreteStridedIntervalSet))
    nose.tools.assert_true(vsa_model(r).collapse().identical(vsa_model(SI(bits=32, stride=1, lower_bound=0, upper_bound=35))))

def test_solution():
    # Set backend
    b = claripy.backends.vsa

    solver_type = claripy.LightFrontend
    s = solver_type(b)

    VS = claripy.ValueSet

    si = claripy.SI(bits=32, stride=10, lower_bound=32, upper_bound=320)
    nose.tools.assert_true(s.solution(si, si))
    nose.tools.assert_true(s.solution(si, 32))
    nose.tools.assert_false(s.solution(si, 31))

    si2 = claripy.SI(bits=32, stride=0, lower_bound=3, upper_bound=3)
    nose.tools.assert_true(s.solution(si2, si2))
    nose.tools.assert_true(s.solution(si2, 3))
    nose.tools.assert_false(s.solution(si2, 18))
    nose.tools.assert_false(s.solution(si2, si))

    vs = VS(region='global', bits=32, val=0xDEADCA7)
    nose.tools.assert_true(s.solution(vs, 0xDEADCA7))
    nose.tools.assert_false(s.solution(vs, 0xDEADBEEF))

    si = claripy.SI(bits=32, stride=0, lower_bound=3, upper_bound=3)
    si2 = claripy.SI(bits=32, stride=10, lower_bound=32, upper_bound=320)
    vs = VS(bits=32)
    vsa_model(vs).merge_si('global', vsa_model(si))
    vsa_model(vs).merge_si('foo', vsa_model(si2))
    nose.tools.assert_true(s.solution(vs, 3))
    nose.tools.assert_true(s.solution(vs, 122))
    nose.tools.assert_true(s.solution(vs, si))
    nose.tools.assert_false(s.solution(vs, 18))
    nose.tools.assert_false(s.solution(vs, 322))

def test_reasonable_bounds():
    si = claripy.SI(bits=32, stride=1, lower_bound=-20, upper_bound=-10)
    b = claripy.backends.vsa
    assert b.max(si) == 0xfffffff6
    assert b.min(si) == 0xffffffec

    si = claripy.SI(bits=32, stride=1, lower_bound=-20, upper_bound=10)
    b = claripy.backends.vsa
    assert b.max(si) == 0xffffffff
    assert b.min(si) == 0

def test_shifting():

    SI = claripy.SI
    identical = claripy.backends.vsa.identical

    # <32>1[2,4] LShR 1 = <32>1[1,2]
    si = SI(bits=32, stride=1, lower_bound=2, upper_bound=4)
    r = si.LShR(1)
    nose.tools.assert_true(identical(r, SI(bits=32, stride=1, lower_bound=1, upper_bound=2)))

    # <32>4[15,11] LShR 4 = <32>1[0, 0xfffffff]
    si = SI(bits=32, stride=4, lower_bound=15, upper_bound=11)
    r = si.LShR(4)
    nose.tools.assert_true(identical(r, SI(bits=32, stride=1, lower_bound=0, upper_bound=0xfffffff)))

    # Extract
    si = SI(bits=32, stride=4, lower_bound=15, upper_bound=11)
    r = si[31:4]
    nose.tools.assert_true(identical(r, SI(bits=28, stride=1, lower_bound=0, upper_bound=0xfffffff)))

    # <32>1[-4,-2] >> 1 = <32>1[-2,-1]
    si = SI(bits=32, stride=1, lower_bound=-4, upper_bound=-2)
    r = (si >> 1)
    nose.tools.assert_true(identical(r, SI(bits=32, stride=1, lower_bound=-2, upper_bound=-1)))

    # <32>1[-4,-2] LShR 1 = <32>1[0x7ffffffe,0x7fffffff]
    si = SI(bits=32, stride=1, lower_bound=-4, upper_bound=-2)
    r = si.LShR(1)
    nose.tools.assert_true(identical(r, SI(bits=32, stride=1, lower_bound=0x7ffffffe, upper_bound=0x7fffffff)))

if __name__ == '__main__':
    test_reasonable_bounds()
    test_reversed_concat()
    test_fucked_extract()
    test_simple_cardinality()
    test_wrapped_intervals()
    test_join()
    test_vsa()
    test_vsa_constraint_to_si()
    test_vsa_discrete_value_set()
    test_solution()
    test_shifting()
