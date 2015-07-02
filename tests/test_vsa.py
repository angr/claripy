import claripy
import nose

from claripy.backends import BackendVSA
from claripy.vsa import TrueResult, MaybeResult, BoolResult, StridedInterval, DiscreteStridedIntervalSet

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
    #VS = clrp.ValueSet
    BVV = clrp.BVV

    # Disable the use of DiscreteStridedIntervalSet
    claripy.vsa.strided_interval.allow_dsis = False

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
    nose.tools.assert_equal(si1.model == 10, TrueResult())
    nose.tools.assert_equal(si2.model == 10, TrueResult())
    nose.tools.assert_equal(si1.model == si2.model, TrueResult())
    # __add__
    si_add_1 = b.convert((si1 + si2))
    nose.tools.assert_equal(si_add_1 == 20, TrueResult())
    si_add_2 = b.convert((si1 + si_a))
    nose.tools.assert_equal(si_add_2 == SI(bits=32, stride=2, lower_bound=20, upper_bound=30).model, TrueResult())
    si_add_3 = b.convert((si_a + si_b))
    nose.tools.assert_equal(si_add_3 == SI(bits=32, stride=2, lower_bound=-90, upper_bound=220).model, TrueResult())
    si_add_4 = b.convert((si_b + si_c))
    nose.tools.assert_equal(si_add_4 == SI(bits=32, stride=1, lower_bound=-200, upper_bound=400).model, TrueResult())
    # __add__ with overflow
    si_add_5 = b.convert(si_h + 0xffffffff)
    nose.tools.assert_equal(si_add_5 == SI(bits=32, stride=0, lower_bound=0x7fffffff, upper_bound=0x7fffffff).model, TrueResult())
    # __sub__
    si_minus_1 = b.convert((si1 - si2))
    nose.tools.assert_equal(si_minus_1 == 0, TrueResult())
    si_minus_2 = b.convert((si_a - si_b))
    nose.tools.assert_equal(si_minus_2 == SI(bits=32, stride=2, lower_bound=-190, upper_bound=120).model, TrueResult())
    si_minus_3 = b.convert((si_b - si_c))
    nose.tools.assert_equal(si_minus_3 == SI(bits=32, stride=1, lower_bound=-300, upper_bound=300).model, TrueResult())
    # __neg__ / __invert__
    si_neg_1 = b.convert((~si1))
    nose.tools.assert_equal(si_neg_1 == -11, TrueResult())
    si_neg_2 = b.convert((~si_b))
    nose.tools.assert_equal(si_neg_2 == SI(bits=32, stride=2, lower_bound=-201, upper_bound=99).model, TrueResult())
    # __or__
    si_or_1 = b.convert(si1 | si3)
    nose.tools.assert_equal(si_or_1 == 30, TrueResult())
    si_or_2 = b.convert(si1 | si2)
    nose.tools.assert_equal(si_or_2 == 10, TrueResult())
    si_or_3 = b.convert(si1 | si_a) # An integer | a strided interval
    nose.tools.assert_equal(si_or_3 == SI(bits=32, stride=2, lower_bound=10, upper_bound=30).model, TrueResult())
    si_or_3 = b.convert(si_a | si1) # Exchange the operands
    nose.tools.assert_equal(si_or_3 == SI(bits=32, stride=2, lower_bound=10, upper_bound=30).model, TrueResult())
    si_or_4 = b.convert(si_a | si_d) # A strided interval | another strided interval
    nose.tools.assert_equal(si_or_4 == SI(bits=32, stride=2, lower_bound=50, upper_bound=62).model, TrueResult())
    si_or_4 = b.convert(si_d | si_a) # Exchange the operands
    nose.tools.assert_equal(si_or_4 == SI(bits=32, stride=2, lower_bound=50, upper_bound=62).model, TrueResult())
    si_or_5 = b.convert(si_e | si_f) #
    nose.tools.assert_equal(si_or_5 == SI(bits=16, stride=1, lower_bound=0x2000, upper_bound=0x30ff).model, TrueResult())
    si_or_6 = b.convert(si_e | si_g) #
    nose.tools.assert_equal(si_or_6 == SI(bits=16, stride=1, lower_bound=0x2000, upper_bound=0x30ff).model, TrueResult())
    # Shifting
    si_shl_1 = b.convert(si1 << 3)
    nose.tools.assert_equal(si_shl_1.bits, 32)
    nose.tools.assert_equal(si_shl_1 == SI(bits=32, stride=0, lower_bound=80, upper_bound=80).model, TrueResult())
    # Multiplication
    si_mul_1 = b.convert(si1 * 3)
    nose.tools.assert_equal(si_mul_1.bits, 32)
    nose.tools.assert_equal(si_mul_1 == SI(bits=32, stride=0, lower_bound=30, upper_bound=30).model, TrueResult())
    si_mul_2 = b.convert(si_a * 3)
    nose.tools.assert_equal(si_mul_2.bits, 32)
    nose.tools.assert_equal(si_mul_2 == SI(bits=32, stride=6, lower_bound=30, upper_bound=60).model, TrueResult())
    si_mul_3 = b.convert(si_a * si_b)
    nose.tools.assert_equal(si_mul_3.bits, 32)
    nose.tools.assert_equal(si_mul_3 == SI(bits=32, stride=2, lower_bound=-2000, upper_bound=4000).model, TrueResult())
    # Division
    si_div_1 = b.convert(si1 / 3)
    nose.tools.assert_equal(si_div_1.bits, 32)
    nose.tools.assert_equal(si_div_1 == SI(bits=32, stride=0, lower_bound=3, upper_bound=3).model, TrueResult())
    si_div_2 = b.convert(si_a / 3)
    nose.tools.assert_equal(si_div_2.bits, 32)
    nose.tools.assert_equal(si_div_2 == SI(bits=32, stride=1, lower_bound=3, upper_bound=6).model, TrueResult())
    # Modulo
    si_mo_1 = b.convert(si1 % 3)
    nose.tools.assert_equal(si_mo_1.bits, 32)
    nose.tools.assert_equal(si_mo_1 == SI(bits=32, stride=0, lower_bound=1, upper_bound=1).model, TrueResult())
    si_mo_2 = b.convert(si_a % 3)
    nose.tools.assert_equal(si_mo_2.bits, 32)
    nose.tools.assert_equal(si_mo_2 == SI(bits=32, stride=1, lower_bound=0, upper_bound=2).model, TrueResult())

    #
    # Extracting the sign bit
    #

    # a negative integer
    si = SI(bits=64, stride=0, lower_bound=-1, upper_bound=-1)
    sb = b.convert(si[63: 63])
    nose.tools.assert_equal(sb == 1, TrueResult())

    # non-positive integers
    si = SI(bits=64, stride=1, lower_bound=-1, upper_bound=0)
    sb = b.convert(si[63: 63])
    nose.tools.assert_equal(sb == SI(bits=1, stride=1, lower_bound=0, upper_bound=1).model,
                            TrueResult())

    # Extracting an integer
    si = SI(bits=64, stride=0, lower_bound=0x7fffffffffff0000, upper_bound=0x7fffffffffff0000)
    part1 = b.convert(si[63 : 32])
    part2 = b.convert(si[31 : 0])
    nose.tools.assert_equal(part1 == SI(bits=32, stride=0, lower_bound=0x7fffffff, upper_bound=0x7fffffff).model, TrueResult())
    nose.tools.assert_equal(part2 == SI(bits=32, stride=0, lower_bound=0xffff0000, upper_bound=0xffff0000).model, TrueResult())

    # Concatenating two integers
    si_concat = b.convert(part1.concat(part2))
    nose.tools.assert_equal(si_concat == si.model, TrueResult())

    # Extracting a SI
    si = clrp.SI(bits=64, stride=0x9, lower_bound=0x1, upper_bound=0xa)
    part1 = b.convert(si[63 : 32])
    part2 = b.convert(si[31 : 0])
    nose.tools.assert_equal(part1 == clrp.SI(bits=32, stride=0, lower_bound=0x0, upper_bound=0x0).model, TrueResult())
    nose.tools.assert_equal(part2 == clrp.SI(bits=32, stride=9, lower_bound=1, upper_bound=10).model, TrueResult())

    # Concatenating two SIs
    si_concat = b.convert(part1.concat(part2))
    nose.tools.assert_equal(si_concat == si.model, TrueResult())

    # Zero-Extend the low part
    si_zeroextended = b.convert(part2.zero_extend(32))
    nose.tools.assert_equal(si_zeroextended == clrp.SI(bits=64, stride=9, lower_bound=1, upper_bound=10).model, TrueResult())

    # Sign-extension
    si_signextended = b.convert(part2.sign_extend(32))
    nose.tools.assert_equal(si_signextended == clrp.SI(bits=64, stride=9, lower_bound=1, upper_bound=10).model, TrueResult())

    # Extract from the result above
    si_extracted = b.convert(si_zeroextended.extract(31, 0))
    nose.tools.assert_equal(si_extracted == clrp.SI(bits=32, stride=9, lower_bound=1, upper_bound=10).model, TrueResult())

    # Union
    si_union_1 = b.convert(si1.union(si2))
    nose.tools.assert_equal(si_union_1 == SI(bits=32, stride=0, lower_bound=10, upper_bound=10).model, TrueResult())
    si_union_2 = b.convert(si1.union(si3))
    nose.tools.assert_equal(si_union_2 == SI(bits=32, stride=18, lower_bound=10, upper_bound=28).model, TrueResult())
    si_union_3 = b.convert(si1.union(si_a))
    nose.tools.assert_equal(si_union_3 == SI(bits=32, stride=2, lower_bound=10, upper_bound=20).model, TrueResult())
    si_union_4 = b.convert(si_a.union(si_b))
    nose.tools.assert_equal(si_union_4 == SI(bits=32, stride=2, lower_bound=-100, upper_bound=200).model, TrueResult())
    si_union_5 = b.convert(si_b.union(si_c))
    nose.tools.assert_equal(si_union_5 == SI(bits=32, stride=1, lower_bound=-100, upper_bound=200).model, TrueResult())

    # Intersection
    si_intersection_1 = b.convert(si1.intersection(si1))
    nose.tools.assert_equal(si_intersection_1 == si2, TrueResult())
    si_intersection_2 = b.convert(si1.intersection(si2))
    nose.tools.assert_equal(si_intersection_2 == SI(bits=32, stride=0, lower_bound=10, upper_bound=10).model, TrueResult())
    si_intersection_3 = b.convert(si1.intersection(si_a))
    nose.tools.assert_equal(si_intersection_3 == SI(bits=32, stride=0, lower_bound=10, upper_bound=10).model, TrueResult())
    si_intersection_4 = b.convert(si_a.intersection(si_b))
    nose.tools.assert_equal(si_intersection_4 == SI(bits=32, stride=2, lower_bound=10, upper_bound=20).model, TrueResult())
    si_intersection_5 = b.convert(si_b.intersection(si_c))
    nose.tools.assert_equal(si_intersection_5 == SI(bits=32, stride=6, lower_bound=-100, upper_bound=200).model, TrueResult())

    # Sign-extension
    si = SI(bits=1, stride=0, lower_bound=1, upper_bound=1)
    si_signextended = si.sign_extend(31)
    nose.tools.assert_equal(si_signextended.model == SI(bits=32, stride=0, lower_bound=0xffffffff, upper_bound=0xffffffff).model, TrueResult())

    # Comparison between SI and BVV
    si = SI(bits=32, stride=1, lower_bound=-0x7f, upper_bound=0x7f)
    si.uninitialized = True
    bvv = BVV(0x30, 32)
    comp = (si < bvv)
    nose.tools.assert_equal(comp.model, MaybeResult())

    # Better extraction
    # si = <32>0x1000000[0xcffffff, 0xdffffff]R
    si = SI(bits=32, stride=0x1000000, lower_bound=0xcffffff, upper_bound=0xdffffff)
    si_byte0 = b.convert(si[7: 0])
    si_byte1 = b.convert(si[15: 8])
    si_byte2 = b.convert(si[23: 16])
    si_byte3 = b.convert(si[31: 24])
    nose.tools.assert_equal(si_byte0 == SI(bits=8, stride=0, lower_bound=0xff, upper_bound=0xff).model, TrueResult())
    nose.tools.assert_equal(si_byte1 == SI(bits=8, stride=0, lower_bound=0xff, upper_bound=0xff).model, TrueResult())
    nose.tools.assert_equal(si_byte2 == SI(bits=8, stride=0, lower_bound=0xff, upper_bound=0xff).model, TrueResult())
    nose.tools.assert_equal(si_byte3 == SI(bits=8, stride=1, lower_bound=0xc, upper_bound=0xd).model, TrueResult())

    # Optimization on bitwise-and
    si_1 = SI(bits=32, stride=1, lower_bound=0x0, upper_bound=0xffffffff)
    si_2 = SI(bits=32, stride=0, lower_bound=0x80000000, upper_bound=0x80000000)
    si = b.convert(si_1 & si_2)
    nose.tools.assert_equal(si == SI(bits=32, stride=0x80000000, lower_bound=0, upper_bound=0x80000000).model,
                            TrueResult())

    si_1 = SI(bits=32, stride=1, lower_bound=0x0, upper_bound=0x7fffffff)
    si_2 = SI(bits=32, stride=0, lower_bound=0x80000000, upper_bound=0x80000000)
    si = b.convert(si_1 & si_2)
    nose.tools.assert_equal(si == SI(bits=32, stride=0, lower_bound=0, upper_bound=0).model, TrueResult())

    #
    # ValueSet
    #

    vs_1 = clrp.ValueSet(bits=32)
    nose.tools.assert_true(vs_1.model.is_empty(), True)
    # Test merging two addresses
    vs_1.model.merge_si('global', si1)
    vs_1.model.merge_si('global', si3)
    nose.tools.assert_equal(vs_1.model.get_si('global') == SI(bits=32, stride=18, lower_bound=10, upper_bound=28).model, TrueResult())
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
    nose.tools.assert_equal(max_val, 0xffffffff)
    nose.tools.assert_equal(min_val, -0x80000000)

    # if_1 = And(VS_2, IfProxy(si == 0, 0, 1))
    vs_2 = clrp.ValueSet(region='global', bits=32, val=0xFA7B00B)
    si = clrp.SI(bits=32, stride=1, lower_bound=0, upper_bound=1)
    if_1 = (vs_2 & clrp.If(si == 0, SI(bits=32, stride=0, lower_bound=0, upper_bound=0), SI(bits=32, stride=0, lower_bound=0xffffffff, upper_bound=0xffffffff)))
    nose.tools.assert_equal(if_1.model.trueexpr == clrp.ValueSet(region='global', bits=32, val=0).model, TrueResult())
    nose.tools.assert_equal(if_1.model.falseexpr == vs_2.model, TrueResult())

    # if_2 = And(VS_3, IfProxy(si != 0, 0, 1)
    vs_3 = clrp.ValueSet(region='global', bits=32, val=0xDEADCA7)
    si = clrp.SI(bits=32, stride=1, lower_bound=0, upper_bound=1)
    if_2 = (vs_3 & clrp.If(si != 0, SI(bits=32, stride=0, lower_bound=0, upper_bound=0), SI(bits=32, stride=0, lower_bound=0xffffffff, upper_bound=0xffffffff)))
    nose.tools.assert_equal(if_2.model.trueexpr == clrp.ValueSet(region='global', bits=32, val=0).model, TrueResult())
    nose.tools.assert_equal(if_2.model.falseexpr == vs_3.model, TrueResult())

    # Something crazy is gonna happen...
    if_3 = if_1 + if_2
    nose.tools.assert_equal(if_3.model.trueexpr == vs_3.model, TrueResult())
    nose.tools.assert_equal(if_3.model.falseexpr == vs_2.model, TrueResult())

def test_vsa_constraint_to_si():
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
        clrp.is_true(falseside_replacement[0][1] == SI(bits=32, stride=1, lower_bound=1, upper_bound=2)))

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
        clrp.is_true(trueside_replacement[0][1] == SI(bits=32, stride=0, lower_bound=0, upper_bound=0)))

    falseside_sat, falseside_replacement = b.constraint_to_si(ast_false)
    nose.tools.assert_equal(falseside_sat, True)
    nose.tools.assert_equal(len(falseside_replacement), 1)
    nose.tools.assert_true(falseside_replacement[0][0] is s2)
    # False side; SI<32>1[1, 2]
    nose.tools.assert_true(
        clrp.is_true(falseside_replacement[0][1] == SI(bits=32, stride=1, lower_bound=1, upper_bound=2)))

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
        clrp.is_true(trueside_replacement[0][1] == SI(bits=32, stride=0, lower_bound=0, upper_bound=0)))

    falseside_sat, falseside_replacement = b.constraint_to_si(ast_false)
    nose.tools.assert_equal(falseside_sat, True)
    nose.tools.assert_equal(len(falseside_replacement), 1)
    nose.tools.assert_true(falseside_replacement[0][0] is s3)
    # False side; SI<32>1[1, 2]
    nose.tools.assert_true(
        clrp.is_true(falseside_replacement[0][1] == SI(bits=32, stride=1, lower_bound=1, upper_bound=2)))

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
        clrp.is_true(trueside_replacement[0][1] == SI(bits=64, stride=1, lower_bound=-0x8000000000000000, upper_bound=-1)))

    falseside_sat, falseside_replacement = b.constraint_to_si(ast_false)
    nose.tools.assert_equal(falseside_sat, True)
    nose.tools.assert_equal(len(falseside_replacement), 1)
    nose.tools.assert_true(falseside_replacement[0][0] is s4)
    # False side; SI<32>1[1, 2]
    nose.tools.assert_true(
        clrp.is_true(falseside_replacement[0][1] == SI(bits=64, stride=1, lower_bound=0, upper_bound=0x7fffffffffffffff)))

    # TODO: Add some more insane test cases

def test_vsa_discrete_value_set():
    """
    Test cases for DiscreteStridedIntervalSet.
    """

    clrp = claripy.Claripies["SerialZ3"]
    # Set backend
    b = BackendVSA()
    b.set_claripy_object(clrp)
    clrp.model_backends.append(b)
    clrp.solver_backends = []

    solver_type = claripy.solvers.BranchingSolver
    s = solver_type(clrp) #pylint:disable=unused-variable

    SI = clrp.StridedInterval
    #VS = clrp.ValueSet
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
    nose.tools.assert_true(r.model.is_empty())

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
    nose.tools.assert_true(BoolResult.is_true(r == SI(bits=32, stride=1, lower_bound=20, upper_bound=55)))
    # r_2 - r_1
    r = r_2 - r_1
    nose.tools.assert_true(isinstance(r.model, DiscreteStridedIntervalSet))
    nose.tools.assert_true(BoolResult.is_true(r == SI(bits=32, stride=1, lower_bound=0, upper_bound=35)))

if __name__ == '__main__':
    test_vsa()
    test_vsa_constraint_to_si()
    test_vsa_discrete_value_set()
