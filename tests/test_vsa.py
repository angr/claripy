import claripy

from claripy.vsa import MaybeResult, BoolResult, DiscreteStridedIntervalSet, StridedInterval, RegionAnnotation

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

    #print(zx, claripy.backends.vsa.convert(zx))
    #print(pre_fucked, claripy.backends.vsa.convert(pre_fucked))
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
    assert claripy.backends.vsa.min(reversed_a) == 0xa000000
    assert claripy.backends.vsa.max(reversed_a) == 0x80000000
    assert claripy.backends.vsa.min(reversed_b) == 0x1000000
    assert claripy.backends.vsa.max(reversed_b) == 0xff000000

    a_concat_b = claripy.Concat(a, b)
    assert a_concat_b._model_vsa._reversed == False

    ra_concat_b = claripy.Concat(reversed_a, b)
    assert ra_concat_b._model_vsa._reversed == False

    a_concat_rb = claripy.Concat(a, reversed_b)
    assert a_concat_rb._model_vsa._reversed == False

    ra_concat_rb = claripy.Concat(reversed_a, reversed_b)
    assert ra_concat_rb._model_vsa._reversed == False

def test_simple_cardinality():
    x = claripy.BVS('x', 32, 0xa, 0x14, 0xa)
    assert x.cardinality == 2

def test_wrapped_intervals():
    #SI = claripy.StridedInterval

    # Disable the use of DiscreteStridedIntervalSet
    claripy.vsa.strided_interval.allow_dsis = False

    #
    # Signedness/unsignedness conversion
    #

    si1 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=0xffffffff)
    assert vsa_model(si1)._signed_bounds() == [ (0x0, 0x7fffffff), (-0x80000000, -0x1) ]
    assert vsa_model(si1)._unsigned_bounds() == [ (0x0, 0xffffffff) ]

    #
    # Pole-splitting
    #

    # south-pole splitting
    si1 = claripy.SI(bits=32, stride=1, lower_bound=-1, upper_bound=1)
    si_list = vsa_model(si1)._ssplit()
    assert len(si_list) == 2
    assert si_list[0].identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=-1, upper_bound=-1)))
    assert si_list[1].identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=1)))

    # north-pole splitting
    si1 = claripy.SI(bits=32, stride=1, lower_bound=-1, upper_bound=-3)
    si_list = vsa_model(si1)._nsplit()
    assert len(si_list) == 2
    assert si_list[0].identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=-1, upper_bound=0x7fffffff)))
    assert si_list[1].identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=0x80000000, upper_bound=-3)))

    # north-pole splitting, episode 2
    si1 = claripy.SI(bits=32, stride=3, lower_bound=3, upper_bound=0)
    si_list = vsa_model(si1)._nsplit()
    assert len(si_list) == 2
    assert si_list[0].identical(vsa_model(claripy.SI(bits=32, stride=3, lower_bound=3, upper_bound=0x7ffffffe)))
    assert si_list[1].identical(vsa_model(claripy.SI(bits=32, stride=3, lower_bound=0x80000001, upper_bound=0)))

    # bipolar splitting
    si1 = claripy.SI(bits=32, stride=1, lower_bound=-2, upper_bound=-8)
    si_list = vsa_model(si1)._psplit()
    assert len(si_list) == 3
    assert si_list[0].identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=-2, upper_bound=-1)))
    assert si_list[1].identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=0x7fffffff)))
    assert si_list[2].identical(vsa_model(claripy.SI(bits=32, stride=1, lower_bound=0x80000000, upper_bound=-8)))

    #
    # Addition
    #

    # Plain addition
    si1 = claripy.SI(bits=32, stride=1, lower_bound=-1, upper_bound=1)
    si2 = claripy.SI(bits=32, stride=1, lower_bound=-1, upper_bound=1)
    si3 = claripy.SI(bits=32, stride=1, lower_bound=-2, upper_bound=2)
    assert claripy.backends.vsa.identical(si1 + si2, si3)
    si4 = claripy.SI(bits=32, stride=1, lower_bound=0xfffffffe, upper_bound=2)
    assert claripy.backends.vsa.identical(si1 + si2, si4)
    si5 = claripy.SI(bits=32, stride=1, lower_bound=2, upper_bound=-2)
    assert not claripy.backends.vsa.identical(si1 + si2, si5)

    # Addition with overflowing cardinality
    si1 = claripy.SI(bits=8, stride=1, lower_bound=0, upper_bound=0xfe)
    si2 = claripy.SI(bits=8, stride=1, lower_bound=0xfe, upper_bound=0xff)
    assert vsa_model((si1 + si2)).is_top

    # Addition that shouldn't get a TOP
    si1 = claripy.SI(bits=8, stride=1, lower_bound=0, upper_bound=0xfe)
    si2 = claripy.SI(bits=8, stride=1, lower_bound=0, upper_bound=0)
    assert not vsa_model((si1 + si2)).is_top

    #
    # Subtraction
    #

    si1 = claripy.SI(bits=8, stride=1, lower_bound=10, upper_bound=15)
    si2 = claripy.SI(bits=8, stride=1, lower_bound=11, upper_bound=12)
    si3 = claripy.SI(bits=8, stride=1, lower_bound=-2, upper_bound=4)
    assert claripy.backends.vsa.identical(si1 - si2, si3)

    #
    # Multiplication
    #

    # integer multiplication
    si1 = claripy.SI(bits=32, to_conv=0xffff)
    si2 = claripy.SI(bits=32, to_conv=0x10000)
    si3 = claripy.SI(bits=32, to_conv=0xffff0000)
    assert claripy.backends.vsa.identical(si1 * si2, si3)

    # intervals multiplication
    si1 = claripy.SI(bits=32, stride=1, lower_bound=10, upper_bound=15)
    si2 = claripy.SI(bits=32, stride=1, lower_bound=20, upper_bound=30)
    si3 = claripy.SI(bits=32, stride=1, lower_bound=200, upper_bound=450)
    assert claripy.backends.vsa.identical(si1 * si2, si3)

    #
    # Division
    #

    # integer division
    si1 = claripy.SI(bits=32, to_conv=10)
    si2 = claripy.SI(bits=32, to_conv=5)
    si3 = claripy.SI(bits=32, to_conv=2)
    assert claripy.backends.vsa.identical(si1 / si2, si3)

    si3 = claripy.SI(bits=32, to_conv=0)
    assert claripy.backends.vsa.identical(si2 / si1, si3)

    # intervals division
    si1 = claripy.SI(bits=32, stride=1, lower_bound=10, upper_bound=100)
    si2 = claripy.SI(bits=32, stride=1, lower_bound=10, upper_bound=20)
    si3 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=10)
    assert claripy.backends.vsa.identical(si1 / si2, si3)

    #
    # Extension
    #

    # zero-extension
    si1 = claripy.SI(bits=8, stride=1, lower_bound=0, upper_bound=0xfd)
    si_zext = si1.zero_extend(32 - 8)
    si_zext_ = claripy.SI(bits=32, stride=1, lower_bound=0x0, upper_bound=0xfd)
    assert claripy.backends.vsa.identical(si_zext, si_zext_)

    # sign-extension
    si1 = claripy.SI(bits=8, stride=1, lower_bound=0, upper_bound=0xfd)
    si_sext = si1.sign_extend(32 - 8)
    si_sext_ = claripy.SI(bits=32, stride=1, lower_bound=0xffffff80, upper_bound=0x7f)
    assert claripy.backends.vsa.identical(si_sext, si_sext_)

    #
    # Comparisons
    #

    # -1 == 0xff
    si1 = claripy.SI(bits=8, stride=1, lower_bound=-1, upper_bound=-1)
    si2 = claripy.SI(bits=8, stride=1, lower_bound=0xff, upper_bound=0xff)
    assert claripy.backends.vsa.is_true(si1 == si2)

    # -2 != 0xff
    si1 = claripy.SI(bits=8, stride=1, lower_bound=-2, upper_bound=-2)
    si2 = claripy.SI(bits=8, stride=1, lower_bound=0xff, upper_bound=0xff)
    assert claripy.backends.vsa.is_true(si1 != si2)

    # [-2, -1] < [1, 2] (signed arithmetic)
    si1 = claripy.SI(bits=8, stride=1, lower_bound=1, upper_bound=2)
    si2 = claripy.SI(bits=8, stride=1, lower_bound=-2, upper_bound=-1)
    assert claripy.backends.vsa.is_true(si2.SLT(si1))

    # [-2, -1] <= [1, 2] (signed arithmetic)
    assert claripy.backends.vsa.is_true(si2.SLE(si1))

    # [0xfe, 0xff] > [1, 2] (unsigned arithmetic)
    assert claripy.backends.vsa.is_true(si2.UGT(si1))

    # [0xfe, 0xff] >= [1, 2] (unsigned arithmetic)
    assert claripy.backends.vsa.is_true(si2.UGE(si1))

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
    assert claripy.backends.vsa.identical(tmp1, SI(bits=8, stride=8, lower_bound=2, upper_bound=10))
    tmp2 = tmp1.union(c)
    assert claripy.backends.vsa.identical(tmp2, SI(bits=8, stride=2, lower_bound=2, upper_bound=120))
    tmp3 = tmp2.union(d).union(e)
    assert claripy.backends.vsa.identical(tmp3, SI(bits=8, stride=2, lower_bound=2, upper_bound=132))

    # union a, b, c, d, e, f => [2, 135] with a stride of 1
    tmp = a.union(b).union(c).union(d).union(e).union(f)
    assert claripy.backends.vsa.identical(tmp, SI(bits=8, stride=1, lower_bound=2, upper_bound=135))

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
    assert claripy.backends.vsa.identical(tmp, SI(bits=8, stride=1, lower_bound=220, upper_bound=135))
    assert 220 in vsa_model(tmp).eval(255)
    assert 225 in vsa_model(tmp).eval(255)
    assert 0 in vsa_model(tmp).eval(255)
    assert 135 in vsa_model(tmp).eval(255)
    assert not 138 in vsa_model(tmp).eval(255)

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
    assert vsa_model(si1).name == "foo"

    # Normalization
    si1 = SI(bits=32, stride=1, lower_bound=10, upper_bound=10)
    assert vsa_model(si1).stride == 0

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

    assert is_equal(si1, claripy.SI(bits=32, to_conv=10))
    assert is_equal(si2, claripy.SI(bits=32, to_conv=10))
    assert is_equal(si1, si2)
    # __add__
    si_add_1 = si1 + si2
    assert is_equal(si_add_1, claripy.SI(bits=32, stride=0, lower_bound=20, upper_bound=20))
    si_add_2 = si1 + si_a
    assert is_equal(si_add_2, claripy.SI(bits=32, stride=2, lower_bound=20, upper_bound=30))
    si_add_3 = si_a + si_b
    assert is_equal(si_add_3, claripy.SI(bits=32, stride=2, lower_bound=-90, upper_bound=220))
    si_add_4 = si_b + si_c
    assert is_equal(si_add_4, claripy.SI(bits=32, stride=1, lower_bound=-200, upper_bound=400))
    # __add__ with overflow
    si_add_5 = si_h + 0xffffffff
    assert is_equal(si_add_5, claripy.SI(bits=32, stride=0, lower_bound=0x7fffffff, upper_bound=0x7fffffff))
    # __sub__
    si_minus_1 = si1 - si2
    assert is_equal(si_minus_1, claripy.SI(bits=32, stride=0, lower_bound=0, upper_bound=0))
    si_minus_2 = si_a - si_b
    assert is_equal(si_minus_2, claripy.SI(bits=32, stride=2, lower_bound=-190, upper_bound=120))
    si_minus_3 = si_b - si_c
    assert is_equal(si_minus_3, claripy.SI(bits=32, stride=1, lower_bound=-300, upper_bound=300))
    # __neg__ / __invert__ / bitwise not
    si_neg_1 = ~si1
    assert is_equal(si_neg_1, claripy.SI(bits=32, to_conv=-11))
    si_neg_2 = ~si_b
    assert is_equal(si_neg_2, claripy.SI(bits=32, stride=2, lower_bound=-201, upper_bound=99))
    # __or__
    si_or_1 = si1 | si3
    assert is_equal(si_or_1, claripy.SI(bits=32, to_conv=30))
    si_or_2 = si1 | si2
    assert is_equal(si_or_2, claripy.SI(bits=32, to_conv=10))
    si_or_3 = si1 | si_a # An integer | a strided interval
    assert is_equal(si_or_3 , claripy.SI(bits=32, stride=2, lower_bound=10, upper_bound=30))
    si_or_3 = si_a | si1 # Exchange the operands
    assert is_equal(si_or_3, claripy.SI(bits=32, stride=2, lower_bound=10, upper_bound=30))
    si_or_4 = si_a | si_d # A strided interval | another strided interval
    assert is_equal(si_or_4, claripy.SI(bits=32, stride=2, lower_bound=50, upper_bound=62))
    si_or_4 = si_d | si_a # Exchange the operands
    assert is_equal(si_or_4, claripy.SI(bits=32, stride=2, lower_bound=50, upper_bound=62))
    si_or_5 = si_e | si_f #
    assert is_equal(si_or_5, claripy.SI(bits=16, stride=1, lower_bound=0x2000, upper_bound=0x30ff))
    si_or_6 = si_e | si_g #
    assert is_equal(si_or_6, claripy.SI(bits=16, stride=1, lower_bound=0x2000, upper_bound=0x30ff))
    # Shifting
    si_shl_1 = si1 << 3
    assert si_shl_1.size() == 32
    assert is_equal(si_shl_1, claripy.SI(bits=32, stride=0, lower_bound=80, upper_bound=80))
    # Multiplication
    si_mul_1 = si1 * 3
    assert si_mul_1.size() == 32
    assert is_equal(si_mul_1, claripy.SI(bits=32, stride=0, lower_bound=30, upper_bound=30))
    si_mul_2 = si_a * 3
    assert si_mul_2.size() == 32
    assert is_equal(si_mul_2, claripy.SI(bits=32, stride=6, lower_bound=30, upper_bound=60))
    si_mul_3 = si_a * si_b
    assert si_mul_3.size() == 32
    assert is_equal(si_mul_3, claripy.SI(bits=32, stride=2, lower_bound=-2000, upper_bound=4000))
    # Division
    si_div_1 = si1 / 3
    assert si_div_1.size() == 32
    assert is_equal(si_div_1, claripy.SI(bits=32, stride=0, lower_bound=3, upper_bound=3))
    si_div_2 = si_a / 3
    assert si_div_2.size() == 32
    assert is_equal(si_div_2, claripy.SI(bits=32, stride=1, lower_bound=3, upper_bound=6))
    # Modulo
    si_mo_1 = si1 % 3
    assert si_mo_1.size() == 32
    assert is_equal(si_mo_1, claripy.SI(bits=32, stride=0, lower_bound=1, upper_bound=1))
    si_mo_2 = si_a % 3
    assert si_mo_2.size() == 32
    assert is_equal(si_mo_2, claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=2))

    #
    # Extracting the sign bit
    #

    # a negative integer
    si = claripy.SI(bits=64, stride=0, lower_bound=-1, upper_bound=-1)
    sb = si[63: 63]
    assert is_equal(sb, claripy.SI(bits=1, to_conv=1))

    # non-positive integers
    si = claripy.SI(bits=64, stride=1, lower_bound=-1, upper_bound=0)
    sb = si[63: 63]
    assert is_equal(sb, claripy.SI(bits=1, stride=1, lower_bound=0, upper_bound=1))

    # Extracting an integer
    si = claripy.SI(bits=64, stride=0, lower_bound=0x7fffffffffff0000, upper_bound=0x7fffffffffff0000)
    part1 = si[63 : 32]
    part2 = si[31 : 0]
    assert is_equal(part1, claripy.SI(bits=32, stride=0, lower_bound=0x7fffffff, upper_bound=0x7fffffff))
    assert is_equal(part2, claripy.SI(bits=32, stride=0, lower_bound=0xffff0000, upper_bound=0xffff0000))

    # Concatenating two integers
    si_concat = part1.concat(part2)
    assert is_equal(si_concat, si)

    # Extracting a claripy.SI
    si = claripy.SI(bits=64, stride=0x9, lower_bound=0x1, upper_bound=0xa)
    part1 = si[63 : 32]
    part2 = si[31 : 0]
    assert is_equal(part1, claripy.SI(bits=32, stride=0, lower_bound=0x0, upper_bound=0x0))
    assert is_equal(part2, claripy.SI(bits=32, stride=9, lower_bound=1, upper_bound=10))

    # Concatenating two claripy.SIs
    si_concat = part1.concat(part2)
    assert is_equal(si_concat, si)

    # Concatenating two SIs that are of different sizes
    si_1 = SI(bits=64, stride=1, lower_bound=0, upper_bound=0xffffffffffffffff)
    si_2 = SI(bits=32, stride=1, lower_bound=0, upper_bound=0xffffffff)
    si_concat = si_1.concat(si_2)
    assert is_equal(si_concat, SI(bits=96, stride=1,                                                   lower_bound=0,                                                   upper_bound=0xffffffffffffffffffffffff))

    # Zero-Extend the low part
    si_zeroextended = part2.zero_extend(32)
    assert is_equal(si_zeroextended, claripy.SI(bits=64, stride=9, lower_bound=1, upper_bound=10))

    # Sign-extension
    si_signextended = part2.sign_extend(32)
    assert is_equal(si_signextended, claripy.SI(bits=64, stride=9, lower_bound=1, upper_bound=10))

    # Extract from the result above
    si_extracted = si_zeroextended[31:0]
    assert is_equal(si_extracted, claripy.SI(bits=32, stride=9, lower_bound=1, upper_bound=10))

    # Union
    si_union_1 = si1.union(si2)
    assert is_equal(si_union_1, claripy.SI(bits=32, stride=0, lower_bound=10, upper_bound=10))
    si_union_2 = si1.union(si3)
    assert is_equal(si_union_2, claripy.SI(bits=32, stride=18, lower_bound=10, upper_bound=28))
    si_union_3 = si1.union(si_a)
    assert is_equal(si_union_3, claripy.SI(bits=32, stride=2, lower_bound=10, upper_bound=20))
    si_union_4 = si_a.union(si_b)
    assert is_equal(si_union_4, claripy.SI(bits=32, stride=2, lower_bound=-100, upper_bound=200))
    si_union_5 = si_b.union(si_c)
    assert is_equal(si_union_5, claripy.SI(bits=32, stride=1, lower_bound=-100, upper_bound=200))

    # Intersection
    si_intersection_1 = si1.intersection(si1)
    assert is_equal(si_intersection_1, si2)
    si_intersection_2 = si1.intersection(si2)
    assert is_equal(si_intersection_2, claripy.SI(bits=32, stride=0, lower_bound=10, upper_bound=10))
    si_intersection_3 = si1.intersection(si_a)
    assert is_equal(si_intersection_3, claripy.SI(bits=32, stride=0, lower_bound=10, upper_bound=10))

    si_intersection_4 = si_a.intersection(si_b)

    assert is_equal(si_intersection_4, claripy.SI(bits=32, stride=2, lower_bound=10, upper_bound=20))
    si_intersection_5 = si_b.intersection(si_c)
    assert is_equal(si_intersection_5, claripy.SI(bits=32, stride=6, lower_bound=-100, upper_bound=200))

    # More intersections
    t0 = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=0x27)
    t1 = claripy.SI(bits=32, stride=0x7fffffff, lower_bound=0x80000002, upper_bound=1)

    si_is_6 = t0.intersection(t1)
    assert is_equal(si_is_6, claripy.SI(bits=32, stride=0, lower_bound=1, upper_bound=1))

    t2 = claripy.SI(bits=32, stride=5, lower_bound=20, upper_bound=30)
    t3 = claripy.SI(bits=32, stride=1, lower_bound=27, upper_bound=0xffffffff)

    si_is_7 = t2.intersection(t3)
    assert is_equal(si_is_7, claripy.SI(bits=32, stride=0, lower_bound=30, upper_bound=30))

    t4 = claripy.SI(bits=32, stride=5, lower_bound=-400, upper_bound=400)
    t5 = claripy.SI(bits=32, stride=1, lower_bound=395, upper_bound=-395)
    si_is_8 = t4.intersection(t5)
    assert is_equal(si_is_8, claripy.SI(bits=32, stride=5, lower_bound=-400, upper_bound=400))

    # Sign-extension
    si = claripy.SI(bits=1, stride=0, lower_bound=1, upper_bound=1)
    si_signextended = si.sign_extend(31)
    assert is_equal(si_signextended, claripy.SI(bits=32, stride=0, lower_bound=0xffffffff, upper_bound=0xffffffff))

    # Comparison between claripy.SI and BVV
    si = claripy.SI(bits=32, stride=1, lower_bound=-0x7f, upper_bound=0x7f)
    si._model_vsa.uninitialized = True
    bvv = BVV(0x30, 32)
    comp = (si < bvv)
    assert vsa_model(comp).identical(MaybeResult())

    # Better extraction
    # si = <32>0x1000000[0xcffffff, 0xdffffff]R
    si = claripy.SI(bits=32, stride=0x1000000, lower_bound=0xcffffff, upper_bound=0xdffffff)
    si_byte0 = si[7: 0]
    si_byte1 = si[15: 8]
    si_byte2 = si[23: 16]
    si_byte3 = si[31: 24]
    assert is_equal(si_byte0, claripy.SI(bits=8, stride=0, lower_bound=0xff, upper_bound=0xff))
    assert is_equal(si_byte1, claripy.SI(bits=8, stride=0, lower_bound=0xff, upper_bound=0xff))
    assert is_equal(si_byte2, claripy.SI(bits=8, stride=0, lower_bound=0xff, upper_bound=0xff))
    assert is_equal(si_byte3, claripy.SI(bits=8, stride=1, lower_bound=0xc, upper_bound=0xd))

    # Optimization on bitwise-and
    si_1 = claripy.SI(bits=32, stride=1, lower_bound=0x0, upper_bound=0xffffffff)
    si_2 = claripy.SI(bits=32, stride=0, lower_bound=0x80000000, upper_bound=0x80000000)
    si = si_1 & si_2
    assert is_equal(si, claripy.SI(bits=32, stride=0x80000000, lower_bound=0, upper_bound=0x80000000))

    si_1 = claripy.SI(bits=32, stride=1, lower_bound=0x0, upper_bound=0x7fffffff)
    si_2 = claripy.SI(bits=32, stride=0, lower_bound=0x80000000, upper_bound=0x80000000)
    si = si_1 & si_2
    assert is_equal(si, claripy.SI(bits=32, stride=0, lower_bound=0, upper_bound=0))

    # Concatenation: concat with zeros only increases the stride
    si_1 = claripy.SI(bits=8, stride=0xff, lower_bound=0x0, upper_bound=0xff)
    si_2 = claripy.SI(bits=8, stride=0, lower_bound=0, upper_bound=0)
    si = si_1.concat(si_2)
    assert is_equal(si, claripy.SI(bits=16, stride=0xff00, lower_bound=0, upper_bound=0xff00))

    # Extract from a reversed value
    si_1 = claripy.SI(bits=64, stride=0xff, lower_bound=0x0, upper_bound=0xff)
    si_2 = si_1.reversed[63 : 56]
    assert is_equal(si_2, claripy.SI(bits=8, stride=0xff, lower_bound=0x0, upper_bound=0xff))

    #
    # ValueSet
    #

    def VS(name=None, bits=None, region=None, val=None):
        region = 'foobar' if region is None else region
        return claripy.ValueSet(bits, region=region, region_base_addr=0, value=val, name=name)

    vs_1 = VS(bits=32, val=0)
    vs_1 = vs_1.intersection(VS(bits=32, val=1))
    assert vsa_model(vs_1).is_empty
    # Test merging two addresses
    vsa_model(vs_1)._merge_si('global', 0, vsa_model(si1))
    vsa_model(vs_1)._merge_si('global', 0, vsa_model(si3))
    assert vsa_model(vs_1).get_si('global').identical(vsa_model(SI(bits=32, stride=18, lower_bound=10, upper_bound=28)))
    # Length of this ValueSet
    assert len(vsa_model(vs_1)) == 32

    vs_1 = VS(name='boo', bits=32, val=0).intersection(VS(name='makeitempty', bits=32, val=1))
    vs_2 = VS(name='foo', bits=32, val=0).intersection(VS(name='makeitempty', bits=32, val=1))
    assert claripy.backends.vsa.identical(vs_1, vs_1)
    assert claripy.backends.vsa.identical(vs_2, vs_2)
    vsa_model(vs_1)._merge_si('global', 0, vsa_model(si1))
    assert not claripy.backends.vsa.identical(vs_1, vs_2)
    vsa_model(vs_2)._merge_si('global', 0, vsa_model(si1))
    assert claripy.backends.vsa.identical(vs_1, vs_2)
    assert claripy.backends.vsa.is_true((vs_1 & vs_2) == vs_1)
    vsa_model(vs_1)._merge_si('global', 0, vsa_model(si3))
    assert not claripy.backends.vsa.identical(vs_1, vs_2)

    # Subtraction
    # Subtraction of two pointers yields a concrete value

    vs_1 = VS(name='foo', region='global', bits=32, val=0x400010)
    vs_2 = VS(name='bar', region='global', bits=32, val=0x400000)
    si = vs_1 - vs_2
    assert type(vsa_model(si)) is StridedInterval
    assert claripy.backends.vsa.identical(si, claripy.SI(bits=32, stride=0, lower_bound=0x10, upper_bound=0x10))

    #
    # IfProxy
    #

    si = claripy.SI(bits=32, stride=1, lower_bound=10, upper_bound=0xffffffff)
    if_0 = claripy.If(si == 0, si, si - 1)
    assert claripy.backends.vsa.identical(if_0, if_0)
    assert not claripy.backends.vsa.identical(if_0, si)

    # max and min on IfProxy
    si = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=0xffffffff)
    if_0 = claripy.If(si == 0, si, si - 1)
    max_val = b.max(if_0)
    min_val = b.min(if_0)
    assert max_val == 0xffffffff
    assert min_val == 0x00000000

    # identical
    assert claripy.backends.vsa.identical(if_0, if_0)
    assert claripy.backends.vsa.identical(if_0, si)
    if_0_copy = claripy.If(si == 0, si, si - 1)
    assert claripy.backends.vsa.identical(if_0, if_0_copy)
    if_1 = claripy.If(si == 1, si, si - 1)
    assert claripy.backends.vsa.identical(if_0, if_1)

    si = SI(bits=32, stride=0, lower_bound=1, upper_bound=1)
    if_0 = claripy.If(si == 0, si, si - 1)
    if_0_copy = claripy.If(si == 0, si, si - 1)
    assert claripy.backends.vsa.identical(if_0, if_0_copy)
    if_1 = claripy.If(si == 1, si, si - 1)
    assert not claripy.backends.vsa.identical(if_0, if_1)
    if_1 = claripy.If(si == 0, si + 1, si - 1)
    assert claripy.backends.vsa.identical(if_0, if_1)
    if_1 = claripy.If(si == 0, si, si)
    assert not claripy.backends.vsa.identical(if_0, if_1)

    # if_1 = And(VS_2, IfProxy(si == 0, 0, 1))
    vs_2 = VS(region='global', bits=32, val=0xFA7B00B)
    si = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=1)
    if_1 = (vs_2 & claripy.If(si == 0, claripy.SI(bits=32, stride=0, lower_bound=0, upper_bound=0), claripy.SI(bits=32, stride=0, lower_bound=0xffffffff, upper_bound=0xffffffff)))
    assert claripy.backends.vsa.is_true(vsa_model(if_1.ite_excavated.args[1]) == vsa_model(VS(region='global', bits=32, val=0)))
    assert claripy.backends.vsa.is_true(vsa_model(if_1.ite_excavated.args[2]) == vsa_model(vs_2))

    # if_2 = And(VS_3, IfProxy(si != 0, 0, 1)
    vs_3 = VS(region='global', bits=32, val=0xDEADCA7)
    si = claripy.SI(bits=32, stride=1, lower_bound=0, upper_bound=1)
    if_2 = (vs_3 & claripy.If(si != 0, claripy.SI(bits=32, stride=0, lower_bound=0, upper_bound=0), claripy.SI(bits=32, stride=0, lower_bound=0xffffffff, upper_bound=0xffffffff)))
