import claripy
import nose

from claripy.backends import BackendVSA
from claripy.vsa import TrueResult, MaybeResult, BoolResult, StridedInterval, DiscreteStridedIntervalSet

def test_wrapped_intervals():
    from claripy.backends import BackendVSA

    clrp = claripy.Claripies["SerialZ3"]
    # Set backend
    b = BackendVSA()
    b.set_claripy_object(clrp)
    clrp.model_backends.append(b)
    clrp.solver_backends = []

    solver_type = claripy.solvers.BranchingSolver
    s = solver_type(clrp)  # pylint:disable=unused-variable

    SI = clrp.StridedInterval
    VS = clrp.ValueSet
    BVV = clrp.BVV

    # Disable the use of DiscreteStridedIntervalSet
    claripy.vsa.strided_interval.allow_dsis = False

    # Plain addition
    si1 = SI(bits=32, stride=1, lower_bound=-1, upper_bound=1)
    si2 = SI(bits=32, stride=1, lower_bound=-1, upper_bound=1)
    si3 = SI(bits=32, stride=1, lower_bound=-2, upper_bound=2)
    nose.tools.assert_true((si1 + si2).identical(si3))
    si4 = SI(bits=32, stride=1, lower_bound=0xfffffffe, upper_bound=2)
    nose.tools.assert_true((si1 + si2).identical(si4))
    si5 = SI(bits=32, stride=1, lower_bound=2, upper_bound=-2)
    nose.tools.assert_false((si1 + si2).identical(si5))

    # Addition with overflowing cardinality
    si1 = SI(bits=8, stride=1, lower_bound=0, upper_bound=0xfe)
    si2 = SI(bits=8, stride=1, lower_bound=0xfe, upper_bound=0xff)
    nose.tools.assert_true((si1 + si2).model.is_top)

    # Addition that shouldn't get a TOP
    si1 = SI(bits=8, stride=1, lower_bound=0, upper_bound=0xfe)
    si2 = SI(bits=8, stride=1, lower_bound=0, upper_bound=0)
    nose.tools.assert_false((si1 + si2).model.is_top)

    # Subtraction
    si1 = SI(bits=8, stride=1, lower_bound=10, upper_bound=15)
    si2 = SI(bits=8, stride=1, lower_bound=11, upper_bound=12)
    si3 = SI(bits=8, stride=1, lower_bound=-2, upper_bound=4)
    nose.tools.assert_true((si1 - si2).identical(si3))

def test_vsa():
    clrp = claripy.Claripies["SerialZ3"]
    # Set backend
    b = BackendVSA()
    b.set_claripy_object(clrp)
    clrp.model_backends.append(b)
    clrp.solver_backends = []

    solver_type = claripy.solvers.BranchingSolver
    s = solver_type(clrp) #pylint:disable=unused-variable

    SI = clrp.StridedInterval
    VS = clrp.ValueSet
    BVV = clrp.BVV

    # Disable the use of DiscreteStridedIntervalSet
    claripy.vsa.strided_interval.allow_dsis = False

    def is_equal(ast_0, ast_1):
        return ast_0.identical(ast_1)

    # Integers
    si1 = SI(bits=32, stride=0, lower_bound=10, upper_bound=10)
    si2 = SI(bits=32, stride=0, lower_bound=10, upper_bound=10)
    si3 = SI(bits=32, stride=0, lower_bound=28, upper_bound=28)
    # Strided intervals
    si_a = SI(bits=32, stride=2, lower_bound=10, upper_bound=20)
    si_b = SI(bits=32, stride=2, lower_bound=-100, upper_bound=200)
    si_c = SI(bits=32, stride=3, lower_bound=-100, upper_bound=200)
    si_d = SI(bits=32, stride=2, lower_bound=50, upper_bound=60)
    si_e = SI(bits=16, stride=1, lower_bound=0x2000, upper_bound=0x3000)
    si_f = SI(bits=16, stride=1, lower_bound=0, upper_bound=255)
    si_g = SI(bits=16, stride=1, lower_bound=0, upper_bound=0xff)
    si_h = SI(bits=32, stride=0, lower_bound=0x80000000, upper_bound=0x80000000)
    nose.tools.assert_true(is_equal(si1, SI(bits=32, to_conv=10)))
    nose.tools.assert_true(is_equal(si2, SI(bits=32, to_conv=10)))
    nose.tools.assert_true(is_equal(si1, si2))
    # __add__
    si_add_1 = si1 + si2
    nose.tools.assert_true(is_equal(si_add_1, SI(bits=32, stride=0, lower_bound=20, upper_bound=20)))
    si_add_2 = si1 + si_a
    nose.tools.assert_true(is_equal(si_add_2, SI(bits=32, stride=2, lower_bound=20, upper_bound=30)))
    si_add_3 = si_a + si_b
    nose.tools.assert_true(is_equal(si_add_3, SI(bits=32, stride=2, lower_bound=-90, upper_bound=220)))
    si_add_4 = si_b + si_c
    nose.tools.assert_true(is_equal(si_add_4, SI(bits=32, stride=1, lower_bound=-200, upper_bound=400)))
    # __add__ with overflow
    si_add_5 = si_h + 0xffffffff
    nose.tools.assert_true(is_equal(si_add_5, SI(bits=32, stride=0, lower_bound=0x7fffffff, upper_bound=0x7fffffff)))
    # __sub__
    si_minus_1 = si1 - si2
    nose.tools.assert_true(is_equal(si_minus_1, SI(bits=32, stride=0, lower_bound=0, upper_bound=0)))
    si_minus_2 = si_a - si_b
    nose.tools.assert_true(is_equal(si_minus_2, SI(bits=32, stride=2, lower_bound=-190, upper_bound=120)))
    si_minus_3 = si_b - si_c
    nose.tools.assert_true(is_equal(si_minus_3, SI(bits=32, stride=1, lower_bound=-300, upper_bound=300)))
    # __neg__ / __invert__
    si_neg_1 = ~si1
    nose.tools.assert_true(is_equal(si_neg_1, SI(bits=32, to_conv=-11)))
    si_neg_2 = ~si_b
    nose.tools.assert_true(is_equal(si_neg_2, SI(bits=32, stride=2, lower_bound=-201, upper_bound=99)))
    # __or__
    si_or_1 = si1 | si3
    nose.tools.assert_true(is_equal(si_or_1, SI(bits=32, to_conv=30)))
    si_or_2 = si1 | si2
    nose.tools.assert_true(is_equal(si_or_2, SI(bits=32, to_conv=10)))
    si_or_3 = si1 | si_a # An integer | a strided interval
    nose.tools.assert_true(is_equal(si_or_3 , SI(bits=32, stride=2, lower_bound=10, upper_bound=30)))
    si_or_3 = si_a | si1 # Exchange the operands
    nose.tools.assert_true(is_equal(si_or_3, SI(bits=32, stride=2, lower_bound=10, upper_bound=30)))
    si_or_4 = si_a | si_d # A strided interval | another strided interval
    nose.tools.assert_true(is_equal(si_or_4, SI(bits=32, stride=2, lower_bound=50, upper_bound=62)))
    si_or_4 = si_d | si_a # Exchange the operands
    nose.tools.assert_true(is_equal(si_or_4, SI(bits=32, stride=2, lower_bound=50, upper_bound=62)))
    si_or_5 = si_e | si_f #
    nose.tools.assert_true(is_equal(si_or_5, SI(bits=16, stride=1, lower_bound=0x2000, upper_bound=0x30ff)))
    si_or_6 = si_e | si_g #
    nose.tools.assert_true(is_equal(si_or_6, SI(bits=16, stride=1, lower_bound=0x2000, upper_bound=0x30ff)))
    # Shifting
    si_shl_1 = si1 << 3
    nose.tools.assert_equal(si_shl_1.size(), 32)
    nose.tools.assert_true(is_equal(si_shl_1, SI(bits=32, stride=0, lower_bound=80, upper_bound=80)))
    # Multiplication
    si_mul_1 = si1 * 3
    nose.tools.assert_equal(si_mul_1.size(), 32)
    nose.tools.assert_true(is_equal(si_mul_1, SI(bits=32, stride=0, lower_bound=30, upper_bound=30)))
    si_mul_2 = si_a * 3
    nose.tools.assert_equal(si_mul_2.size(), 32)
    nose.tools.assert_true(is_equal(si_mul_2, SI(bits=32, stride=6, lower_bound=30, upper_bound=60)))
    si_mul_3 = si_a * si_b
    nose.tools.assert_equal(si_mul_3.size(), 32)
    nose.tools.assert_true(is_equal(si_mul_3, SI(bits=32, stride=2, lower_bound=-2000, upper_bound=4000)))
    # Division
    si_div_1 = si1 / 3
    nose.tools.assert_equal(si_div_1.size(), 32)
    nose.tools.assert_true(is_equal(si_div_1, SI(bits=32, stride=0, lower_bound=3, upper_bound=3)))
    si_div_2 = si_a / 3
    nose.tools.assert_equal(si_div_2.size(), 32)
    nose.tools.assert_true(is_equal(si_div_2, SI(bits=32, stride=1, lower_bound=3, upper_bound=6)))
    # Modulo
    si_mo_1 = si1 % 3
    nose.tools.assert_equal(si_mo_1.size(), 32)
    nose.tools.assert_true(is_equal(si_mo_1, SI(bits=32, stride=0, lower_bound=1, upper_bound=1)))
    si_mo_2 = si_a % 3
    nose.tools.assert_equal(si_mo_2.size(), 32)
    nose.tools.assert_true(is_equal(si_mo_2, SI(bits=32, stride=1, lower_bound=0, upper_bound=2)))

    #
    # Extracting the sign bit
    #

    # a negative integer
    si = SI(bits=64, stride=0, lower_bound=-1, upper_bound=-1)
    sb = si[63: 63]
    nose.tools.assert_true(is_equal(sb, SI(bits=1, to_conv=1)))

    # non-positive integers
    si = SI(bits=64, stride=1, lower_bound=-1, upper_bound=0)
    sb = si[63: 63]
    nose.tools.assert_true(is_equal(sb, SI(bits=1, stride=1, lower_bound=0, upper_bound=1)))

    # Extracting an integer
    si = SI(bits=64, stride=0, lower_bound=0x7fffffffffff0000, upper_bound=0x7fffffffffff0000)
    part1 = si[63 : 32]
    part2 = si[31 : 0]
    nose.tools.assert_true(is_equal(part1, SI(bits=32, stride=0, lower_bound=0x7fffffff, upper_bound=0x7fffffff)))
    nose.tools.assert_true(is_equal(part2, SI(bits=32, stride=0, lower_bound=0xffff0000, upper_bound=0xffff0000)))

    # Concatenating two integers
    si_concat = part1.concat(part2)
    nose.tools.assert_true(is_equal(si_concat, si))

    # Extracting a SI
    si = clrp.SI(bits=64, stride=0x9, lower_bound=0x1, upper_bound=0xa)
    part1 = si[63 : 32]
    part2 = si[31 : 0]
    nose.tools.assert_true(is_equal(part1, SI(bits=32, stride=0, lower_bound=0x0, upper_bound=0x0)))
    nose.tools.assert_true(is_equal(part2, SI(bits=32, stride=9, lower_bound=1, upper_bound=10)))

    # Concatenating two SIs
    si_concat = part1.concat(part2)
    nose.tools.assert_true(is_equal(si_concat, si))

    # Zero-Extend the low part
    si_zeroextended = part2.zero_extend(32)
    nose.tools.assert_true(is_equal(si_zeroextended, SI(bits=64, stride=9, lower_bound=1, upper_bound=10)))

    # Sign-extension
    si_signextended = part2.sign_extend(32)
    nose.tools.assert_true(is_equal(si_signextended, SI(bits=64, stride=9, lower_bound=1, upper_bound=10)))

    # Extract from the result above
    si_extracted = si_zeroextended[31:0]
    nose.tools.assert_true(is_equal(si_extracted, SI(bits=32, stride=9, lower_bound=1, upper_bound=10)))

    # Union
    si_union_1 = si1.union(si2)
    nose.tools.assert_true(is_equal(si_union_1, SI(bits=32, stride=0, lower_bound=10, upper_bound=10)))
    si_union_2 = si1.union(si3)
    nose.tools.assert_true(is_equal(si_union_2, SI(bits=32, stride=18, lower_bound=10, upper_bound=28)))
    si_union_3 = si1.union(si_a)
    nose.tools.assert_true(is_equal(si_union_3, SI(bits=32, stride=2, lower_bound=10, upper_bound=20)))
    si_union_4 = si_a.union(si_b)
    nose.tools.assert_true(is_equal(si_union_4, SI(bits=32, stride=2, lower_bound=-100, upper_bound=200)))
    si_union_5 = si_b.union(si_c)
    nose.tools.assert_true(is_equal(si_union_5, SI(bits=32, stride=1, lower_bound=-100, upper_bound=200)))

    # Intersection
    si_intersection_1 = si1.intersection(si1)
    nose.tools.assert_true(is_equal(si_intersection_1, si2))
    si_intersection_2 = si1.intersection(si2)
    nose.tools.assert_true(is_equal(si_intersection_2, SI(bits=32, stride=0, lower_bound=10, upper_bound=10)))
    si_intersection_3 = si1.intersection(si_a)
    nose.tools.assert_true(is_equal(si_intersection_3, SI(bits=32, stride=0, lower_bound=10, upper_bound=10)))
    si_intersection_4 = si_a.intersection(si_b)
    nose.tools.assert_true(is_equal(si_intersection_4, SI(bits=32, stride=2, lower_bound=10, upper_bound=20)))
    si_intersection_5 = si_b.intersection(si_c)
    nose.tools.assert_true(is_equal(si_intersection_5, SI(bits=32, stride=6, lower_bound=-100, upper_bound=200)))

    # Sign-extension
    si = SI(bits=1, stride=0, lower_bound=1, upper_bound=1)
    si_signextended = si.sign_extend(31)
    nose.tools.assert_true(is_equal(si_signextended, SI(bits=32, stride=0, lower_bound=0xffffffff, upper_bound=0xffffffff)))

    # Comparison between SI and BVV
    si = SI(bits=32, stride=1, lower_bound=-0x7f, upper_bound=0x7f)
    si.uninitialized = True
    bvv = BVV(0x30, 32)
    comp = (si < bvv)
    nose.tools.assert_equal(comp.model, MaybeResult())

    # Better extraction
    # si = <32>0x1000000[0xcffffff, 0xdffffff]R
    si = SI(bits=32, stride=0x1000000, lower_bound=0xcffffff, upper_bound=0xdffffff)
    si_byte0 = si[7: 0]
    si_byte1 = si[15: 8]
    si_byte2 = si[23: 16]
    si_byte3 = si[31: 24]
    nose.tools.assert_true(is_equal(si_byte0, SI(bits=8, stride=0, lower_bound=0xff, upper_bound=0xff)))
    nose.tools.assert_true(is_equal(si_byte1, SI(bits=8, stride=0, lower_bound=0xff, upper_bound=0xff)))
    nose.tools.assert_true(is_equal(si_byte2, SI(bits=8, stride=0, lower_bound=0xff, upper_bound=0xff)))
    nose.tools.assert_true(is_equal(si_byte3, SI(bits=8, stride=1, lower_bound=0xc, upper_bound=0xd)))

    # Optimization on bitwise-and
    si_1 = SI(bits=32, stride=1, lower_bound=0x0, upper_bound=0xffffffff)
    si_2 = SI(bits=32, stride=0, lower_bound=0x80000000, upper_bound=0x80000000)
    si = si_1 & si_2
    nose.tools.assert_true(is_equal(si, SI(bits=32, stride=0x80000000, lower_bound=0, upper_bound=0x80000000)))

    si_1 = SI(bits=32, stride=1, lower_bound=0x0, upper_bound=0x7fffffff)
    si_2 = SI(bits=32, stride=0, lower_bound=0x80000000, upper_bound=0x80000000)
    si = si_1 & si_2
    nose.tools.assert_true(is_equal(si, SI(bits=32, stride=0, lower_bound=0, upper_bound=0)))

    #
    # ValueSet
    #

    vs_1 = clrp.ValueSet(bits=32)
    nose.tools.assert_true(vs_1.model.is_empty, True)
    # Test merging two addresses
    vs_1.model.merge_si('global', si1)
    vs_1.model.merge_si('global', si3)
    nose.tools.assert_true(vs_1.model.get_si('global').identical(SI(bits=32, stride=18, lower_bound=10, upper_bound=28).model))
    # Length of this ValueSet
    nose.tools.assert_equal(len(vs_1.model), 32)

    #
    # IfProxy
    #

    # max and min on IfProxy
    si = SI(bits=32, stride=1, lower_bound=0, upper_bound=0xffffffff)
    if_0 = clrp.If(si == 0, si, si - 1)
    max_val = b.max(if_0)
    min_val = b.min(if_0)
    nose.tools.assert_true(max_val, 0xffffffff)
    nose.tools.assert_true(min_val, -0x80000000)

    # if_1 = And(VS_2, IfProxy(si == 0, 0, 1))
    vs_2 = VS(region='global', bits=32, val=0xFA7B00B)
    si = SI(bits=32, stride=1, lower_bound=0, upper_bound=1)
    if_1 = (vs_2 & clrp.If(si == 0, SI(bits=32, stride=0, lower_bound=0, upper_bound=0), SI(bits=32, stride=0, lower_bound=0xffffffff, upper_bound=0xffffffff)))
    nose.tools.assert_true(clrp.is_true(if_1.model.trueexpr == VS(region='global', bits=32, val=0).model))
    nose.tools.assert_true(clrp.is_true(if_1.model.falseexpr == vs_2.model))

    # if_2 = And(VS_3, IfProxy(si != 0, 0, 1)
    vs_3 = clrp.ValueSet(region='global', bits=32, val=0xDEADCA7)
    si = clrp.SI(bits=32, stride=1, lower_bound=0, upper_bound=1)
    if_2 = (vs_3 & clrp.If(si != 0, SI(bits=32, stride=0, lower_bound=0, upper_bound=0), SI(bits=32, stride=0, lower_bound=0xffffffff, upper_bound=0xffffffff)))
    nose.tools.assert_true(clrp.is_true(if_2.model.trueexpr == VS(region='global', bits=32, val=0).model))
    nose.tools.assert_true(clrp.is_true(if_2.model.falseexpr == vs_3.model))

    # Something crazy is gonna happen...
    if_3 = if_1 + if_2
    nose.tools.assert_true(clrp.is_true(if_3.model.trueexpr == vs_3.model))
    nose.tools.assert_true(clrp.is_true(if_3.model.falseexpr == vs_2.model))

def test_vsa_constraint_to_si():
    from claripy.backends import BackendVSA
    from claripy.vsa import TrueResult, FalseResult, MaybeResult  # pylint:disable=unused-variable

    clrp = claripy.Claripies["SerialZ3"]
    # Set backend
    b = BackendVSA()
    b.set_claripy_object(clrp)
    clrp.model_backends.append(b)
    clrp.solver_backends = [ ]

    solver_type = claripy.solvers.BranchingSolver
    s = solver_type(clrp)  #pylint:disable=unused-variable

    SI = clrp.SI
    BVV = clrp.BVV

    claripy.vsa.strided_interval.allow_dsis = False

    #
    # If(SI == 0, 1, 0) == 1
    #

    s1 = SI(bits=32, stride=1, lower_bound=0, upper_bound=2)
    ast_true = (clrp.If(s1 == BVV(0, 32), BVV(1, 1), BVV(0, 1)) == BVV(1, 1))
    ast_false = (clrp.If(s1 == BVV(0, 32), BVV(1, 1), BVV(0, 1)) != BVV(1, 1))

    trueside_sat, trueside_replacement = b.constraint_to_si(ast_true)
    nose.tools.assert_equal(trueside_sat, True)
    nose.tools.assert_equal(len(trueside_replacement), 1)
    nose.tools.assert_true(trueside_replacement[0][0] is s1)
    # True side: SI<32>0[0, 0]
    nose.tools.assert_true(
        clrp.is_true(trueside_replacement[0][1] == SI(bits=32, stride=0, lower_bound=0, upper_bound=0)))

    falseside_sat, falseside_replacement = b.constraint_to_si(ast_false)
    nose.tools.assert_equal(falseside_sat, True)
    nose.tools.assert_equal(len(falseside_replacement), 1)
    nose.tools.assert_true(falseside_replacement[0][0] is s1)
    # False side; SI<32>1[1, 2]
    nose.tools.assert_true(
        clrp.is_true(falseside_replacement[0][1].identical(SI(bits=32, stride=1, lower_bound=1, upper_bound=2))))

    #
    # Extract(0, 0, Concat(BVV(0, 63), If(SI == 0, 1, 0))) == 1
    #

    s2 = SI(bits=32, stride=1, lower_bound=0, upper_bound=2)
    ast_true = (clrp.Extract(0, 0, clrp.Concat(BVV(0, 63), clrp.If(s2 == 0, BVV(1, 1), BVV(0, 1)))) == 1)
    ast_false = (clrp.Extract(0, 0, clrp.Concat(BVV(0, 63), clrp.If(s2 == 0, BVV(1, 1), BVV(0, 1)))) != 1)

    trueside_sat, trueside_replacement = b.constraint_to_si(ast_true)
    nose.tools.assert_equal(trueside_sat, True)
    nose.tools.assert_equal(len(trueside_replacement), 1)
    nose.tools.assert_true(trueside_replacement[0][0] is s2)
    # True side: SI<32>0[0, 0]
    nose.tools.assert_true(
        clrp.is_true(trueside_replacement[0][1].identical(SI(bits=32, stride=0, lower_bound=0, upper_bound=0))))

    falseside_sat, falseside_replacement = b.constraint_to_si(ast_false)
    nose.tools.assert_equal(falseside_sat, True)
    nose.tools.assert_equal(len(falseside_replacement), 1)
    nose.tools.assert_true(falseside_replacement[0][0] is s2)
    # False side; SI<32>1[1, 2]
    nose.tools.assert_true(
        clrp.is_true(falseside_replacement[0][1].identical(SI(bits=32, stride=1, lower_bound=1, upper_bound=2))))

    #
    # Extract(0, 0, ZeroExt(32, If(SI == 0, BVV(1, 32), BVV(0, 32)))) == 1
    #

    s3 = SI(bits=32, stride=1, lower_bound=0, upper_bound=2)
    ast_true = (clrp.Extract(0, 0, clrp.ZeroExt(32, clrp.If(s3 == 0, BVV(1, 32), BVV(0, 32)))) == 1)
    ast_false = (clrp.Extract(0, 0, clrp.ZeroExt(32, clrp.If(s3 == 0, BVV(1, 32), BVV(0, 32)))) != 1)

    trueside_sat, trueside_replacement = b.constraint_to_si(ast_true)
    nose.tools.assert_equal(trueside_sat, True)
    nose.tools.assert_equal(len(trueside_replacement), 1)
    nose.tools.assert_true(trueside_replacement[0][0] is s3)
    # True side: SI<32>0[0, 0]
    nose.tools.assert_true(
        clrp.is_true(trueside_replacement[0][1].identical(SI(bits=32, stride=0, lower_bound=0, upper_bound=0))))

    falseside_sat, falseside_replacement = b.constraint_to_si(ast_false)
    nose.tools.assert_equal(falseside_sat, True)
    nose.tools.assert_equal(len(falseside_replacement), 1)
    nose.tools.assert_true(falseside_replacement[0][0] is s3)
    # False side; SI<32>1[1, 2]
    nose.tools.assert_true(
        clrp.is_true(falseside_replacement[0][1].identical(SI(bits=32, stride=1, lower_bound=1, upper_bound=2))))

    #
    # Extract(0, 0, ZeroExt(32, If(Extract(32, 0, (SI & SI)) < 0, BVV(1, 1), BVV(0, 1))))
    #

    s4 = SI(bits=64, stride=1, lower_bound=0, upper_bound=0xffffffffffffffff)
    ast_true = (
        clrp.Extract(0, 0, clrp.ZeroExt(32, clrp.If(clrp.Extract(31, 0, (s4 & s4)) < 0, BVV(1, 32), BVV(0, 32)))) == 1)
    ast_false = (
        clrp.Extract(0, 0, clrp.ZeroExt(32, clrp.If(clrp.Extract(31, 0, (s4 & s4)) < 0, BVV(1, 32), BVV(0, 32)))) != 1)

    trueside_sat, trueside_replacement = b.constraint_to_si(ast_true)
    nose.tools.assert_equal(trueside_sat, True)
    nose.tools.assert_equal(len(trueside_replacement), 1)
    nose.tools.assert_true(trueside_replacement[0][0] is s4)
    # True side: SI<32>0[0, 0]
    nose.tools.assert_true(
        clrp.is_true(trueside_replacement[0][1].identical(SI(bits=64, stride=1, lower_bound=-0x8000000000000000, upper_bound=-1))))

    falseside_sat, falseside_replacement = b.constraint_to_si(ast_false)
    nose.tools.assert_equal(falseside_sat, True)
    nose.tools.assert_equal(len(falseside_replacement), 1)
    nose.tools.assert_true(falseside_replacement[0][0] is s4)
    # False side; SI<32>1[1, 2]
    nose.tools.assert_true(
        clrp.is_true(falseside_replacement[0][1].identical(SI(bits=64, stride=1, lower_bound=0, upper_bound=0x7fffffffffffffff))))

    # TODO: Add some more insane test cases

def test_vsa_discrete_value_set():
    """
    Test cases for DiscreteStridedIntervalSet.
    """
    from claripy.backends import BackendVSA
    from claripy.vsa import BoolResult, StridedInterval, DiscreteStridedIntervalSet #pylint:disable=unused-variable

    clrp = claripy.Claripies["SerialZ3"]
    # Set backend
    b = BackendVSA()
    b.set_claripy_object(clrp)
    clrp.model_backends.append(b)
    clrp.solver_backends = []

    solver_type = claripy.solvers.BranchingSolver
    s = solver_type(clrp) #pylint:disable=unused-variable

    SI = clrp.StridedInterval
    VS = clrp.ValueSet
    BVV = clrp.BVV

    # Allow the use of DiscreteStridedIntervalSet (cuz we wanna test it!)
    claripy.vsa.strided_interval.allow_dsis = True

    #
    # Union
    #
    val_1 = BVV(0, 32)
    val_2 = BVV(1, 32)
    r = val_1.union(val_2)
    nose.tools.assert_true(isinstance(r.model, DiscreteStridedIntervalSet))
    nose.tools.assert_true(r.model.collapse(), SI(bits=32, stride=1, lower_bound=0, upper_bound=1))

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
    nose.tools.assert_true(isinstance(r.model, StridedInterval))
    nose.tools.assert_true(r.model.is_empty)

    val_1 = SI(bits=32, stride=1, lower_bound=0, upper_bound=10)
    val_2 = SI(bits=32, stride=1, lower_bound=10, upper_bound=20)
    val_3 = SI(bits=32, stride=1, lower_bound=15, upper_bound=50)
    r = val_1.union(val_2)
    nose.tools.assert_true(isinstance(r.model, DiscreteStridedIntervalSet))
    r = r.intersection(val_3)
    nose.tools.assert_equal(sorted(b.eval(r, 100)), [ 15, 16, 17, 18, 19, 20 ])

    #
    # Some logical operations
    #

    val_1 = SI(bits=32, stride=1, lower_bound=0, upper_bound=10)
    val_2 = SI(bits=32, stride=1, lower_bound=5, upper_bound=20)
    r_1 = val_1.union(val_2)
    val_3 = SI(bits=32, stride=1, lower_bound=20, upper_bound=30)
    val_4 = SI(bits=32, stride=1, lower_bound=25, upper_bound=35)
    r_2 = val_3.union(val_4)
    nose.tools.assert_true(isinstance(r_1.model, DiscreteStridedIntervalSet))
    nose.tools.assert_true(isinstance(r_2.model, DiscreteStridedIntervalSet))
    # r_1 < r_2
    nose.tools.assert_true(BoolResult.is_maybe(r_1 < r_2))
    # r_1 <= r_2
    nose.tools.assert_true(BoolResult.is_true(r_1 <= r_2))
    # r_1 >= r_2
    nose.tools.assert_true(BoolResult.is_maybe(r_1 >= r_2))
    # r_1 > r_2
    nose.tools.assert_true(BoolResult.is_false(r_1 > r_2))
    # r_1 == r_2
    nose.tools.assert_true(BoolResult.is_maybe(r_1 == r_2))
    # r_1 != r_2
    nose.tools.assert_true(BoolResult.is_maybe(r_1 != r_2))

    #
    # Some arithmetic operations
    #

    val_1 = SI(bits=32, stride=1, lower_bound=0, upper_bound=10)
    val_2 = SI(bits=32, stride=1, lower_bound=5, upper_bound=20)
    r_1 = val_1.union(val_2)
    val_3 = SI(bits=32, stride=1, lower_bound=20, upper_bound=30)
    val_4 = SI(bits=32, stride=1, lower_bound=25, upper_bound=35)
    r_2 = val_3.union(val_4)
    nose.tools.assert_true(isinstance(r_1.model, DiscreteStridedIntervalSet))
    nose.tools.assert_true(isinstance(r_2.model, DiscreteStridedIntervalSet))
    # r_1 + r_2
    r = r_1 + r_2
    nose.tools.assert_true(isinstance(r.model, DiscreteStridedIntervalSet))
    nose.tools.assert_true(r.model.collapse().identical(SI(bits=32, stride=1, lower_bound=20, upper_bound=55).model))
    # r_2 - r_1
    r = r_2 - r_1
    nose.tools.assert_true(isinstance(r.model, DiscreteStridedIntervalSet))
    nose.tools.assert_true(r.model.collapse().identical(SI(bits=32, stride=1, lower_bound=0, upper_bound=35).model))

if __name__ == '__main__':
    test_vsa()
    test_vsa_constraint_to_si()
    test_vsa_discrete_value_set()
    test_wrapped_intervals()
