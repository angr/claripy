import claripy


def test_bool_simplification():
    def assert_correct(a, b):
        assert claripy.backends.z3.identical(claripy.simplify(a), b)

    a, b, c = (claripy.BoolS(name) for name in ("a", "b", "c"))

    assert_correct(claripy.And(a, claripy.Not(a)), claripy.false)
    assert_correct(claripy.Or(a, claripy.Not(a)), claripy.true)

    complex_true_expression = claripy.Or(
        claripy.And(a, b),
        claripy.Or(claripy.And(a, claripy.Not(b)), claripy.And(claripy.Not(a), c)),
        claripy.Or(claripy.And(a, claripy.Not(b)), claripy.And(claripy.Not(a), claripy.Not(c))),
    )
    assert_correct(complex_true_expression, claripy.true)


def test_simplification():
    def assert_correct(a, b):
        assert claripy.backends.z3.identical(a, b)

    x, y, z = (claripy.BVS(name, 32) for name in ("x", "y", "z"))

    # test extraction of concatted values
    concatted = claripy.Concat(x, y, z)

    assert_correct(concatted[95:64], x)
    assert_correct(concatted[63:32], y)
    assert_correct(concatted[31:0], z)

    assert_correct(concatted[95:32], claripy.Concat(x, y))
    assert_correct(concatted[63:0], claripy.Concat(y, z))

    assert_correct(concatted[95:0], concatted)

    assert_correct(concatted[47:0], claripy.Concat(y, z)[47:0])
    assert_correct(concatted[70:0], concatted[70:0])
    assert_correct(concatted[70:15], concatted[70:15])
    assert_correct(concatted[70:35], claripy.Concat(x, y)[38:3])

    # test extraction of nested concats
    concatted_nested = claripy.Concat(claripy.Reverse(claripy.Concat(x, y)), z)
    assert_correct(concatted_nested[63:0], claripy.Concat(claripy.Reverse(x), z))

    # make sure the division simplification works
    assert_correct(2 + x, claripy.backends.z3.simplify(1 + x + 1))
    assert_correct(x / y, claripy.backends.z3.simplify(x / y))
    assert_correct(x % y, claripy.backends.z3.simplify(x % y))


def test_rotate_shift_mask_simplification():
    a = claripy.BVS("N", 32, max=0xC, min=0x1)
    extend_ = claripy.BVS("extend", 32, uninitialized=True)
    a_ext = extend_.concat(a)
    expr = ((a_ext << 3) | (claripy.LShR(a_ext, 61))) & 0x7FFFFFFF8
    # print(expr)
    # print(expr._model_vsa)
    model_vsa = expr._model_vsa
    assert model_vsa.lower_bound == 8
    assert model_vsa.upper_bound == 0x60
    assert model_vsa.cardinality == 12


def test_reverse_extract_reverse_simplification():
    # without the reverse_extract_reverse simplifier, loading dx from rdx will result in the following complicated
    # expression:
    #   Reverse(Extract(63, 48, Reverse(BVS('rdx', 64))))

    a = claripy.BVS("rdx", 64)
    dx = claripy.Reverse(claripy.Extract(63, 48, claripy.Reverse(a)))

    # simplification should have kicked in at this moment
    assert dx.op == "Extract"
    assert dx.args[0] == 15
    assert dx.args[1] == 0
    assert dx.args[2] is a


def test_reverse_concat_reverse_simplification():
    # Reverse(Concat(Reverse(a), Reverse(b))) = Concat(b, a)

    a = claripy.BVS("a", 32)
    b = claripy.BVS("b", 32)
    x = claripy.Reverse(claripy.Concat(claripy.Reverse(a), claripy.Reverse(b)))

    assert x.op == "Concat"
    assert x.args[0] is b
    assert x.args[1] is a


def perf_boolean_and_simplification_0():
    # Create a gigantic And AST with many operands, one variable at a time
    bool_vars = [claripy.BoolS("b%d" % i) for i in range(1500)]
    v = bool_vars[0]
    for i in range(1, len(bool_vars)):
        v = claripy.And(v, bool_vars[i])


def perf_boolean_and_simplification_1():
    # Create a gigantic And AST with many operands, many variables at a time
    bool_vars = [claripy.BoolS("b%d" % i) for i in range(500)]
    v = bool_vars[0]
    for i in range(1, len(bool_vars)):
        if v.op == "And":
            v = claripy.And(*(v.args + (bool_vars[i] == False,)))  # pylint:disable=singleton-comparison
        else:
            v = claripy.And(v, bool_vars[i])


def test_concrete_flatten():
    a = claripy.BVS("a", 32)
    b = a + 10
    c = 10 + b
    d = a + 20
    assert c is d

    # to future test writers or debuggers: whether the answer is b_neg or b is not particularly important
    e = a - 10
    f = e + 20
    b_neg = a - -10
    assert f is b_neg

    g = e - 10
    h = a - 20
    assert g is h

    i = d - 10
    assert i is b


def test_mask_eq_constant():
    # <Bool ((0#48 .. (0x0 .. sim_data_4_31_8[0:0])[15:0]) & 0xffff) == 0x0>

    a = claripy.BVS("sim_data", 8, explicit_name=True)
    expr = (claripy.ZeroExt(48, claripy.Extract(15, 0, claripy.Concat(claripy.BVV(0, 63), a[0:0]))) & 0xFFFF) == 0x0

    assert expr.op == "__eq__"
    assert expr.args[0].op == "Extract"
    assert expr.args[0].args[0] == 0 and expr.args[0].args[1] == 0
    assert expr.args[0].args[2] is a
    assert expr.args[1].op == "BVV" and expr.args[1].args == (0, 1)

    # the highest bit of the mask (0x1fff) is not aligned to 8
    # we want the mask to be BVV(16, 0x1fff) instead of BVV(13, 0x1fff)
    a = claripy.BVS("sim_data", 8, explicit_name=True)
    expr = (claripy.ZeroExt(48, claripy.Extract(15, 0, claripy.Concat(claripy.BVV(0, 63), a[0:0]))) & 0x1FFF) == 0x0

    assert expr.op == "__eq__"
    assert expr.args[0].op == "__and__"
    _, arg1 = expr.args[0].args
    assert arg1.size() == 16
    assert arg1.args[0] == 0x1FFF


def test_and_mask_comparing_against_constant_simplifier():
    # A & mask == b  ==>  Extract(_, _, A) == Extract(_, _, b) iff high bits of a and b are zeros
    a = claripy.BVS("a", 8)
    b = claripy.BVV(0x10, 32)

    expr = claripy.ZeroExt(24, a) & 0xFFFF == b
    assert expr is (a == 16)

    expr = claripy.Concat(claripy.BVV(0, 24), a) & 0xFFFF == b
    assert expr is (a == 16)

    # A & mask != b ==> Extract(_, _, A) != Extract(_, _, b) iff high bits of a and b are zeros
    a = claripy.BVS("a", 8)
    b = claripy.BVV(0x102000AA, 32)

    expr = claripy.ZeroExt(24, a) & 0xFFFF == b
    assert expr.is_false()

    expr = claripy.Concat(claripy.BVV(0, 24), a) & 0xFFFF == b
    assert expr.is_false()

    # A & 0 == 0 ==> true
    a = claripy.BVS("a", 32)
    b = claripy.BVV(0, 32)
    expr = (a & 0) == b
    assert expr.is_true()
    expr = (a & 0) == claripy.BVV(1, 32)
    assert expr.is_false()


def test_zeroext_extract_comparing_against_constant_simplifier():
    a = claripy.BVS("a", 8, explicit_name=True)
    b = claripy.BVV(0x28, 16)

    expr = claripy.Extract(15, 0, claripy.ZeroExt(24, a)) == b
    assert expr is (a == claripy.BVV(0x28, 8))

    expr = claripy.Extract(7, 0, claripy.ZeroExt(24, a)) == claripy.BVV(0x28, 8)
    assert expr is (a == claripy.BVV(0x28, 8))

    expr = claripy.Extract(7, 0, claripy.ZeroExt(1, a)) == claripy.BVV(0x28, 8)
    assert expr is (a == claripy.BVV(0x28, 8))

    expr = claripy.Extract(6, 0, claripy.ZeroExt(24, a)) == claripy.BVV(0x28, 7)
    assert expr.op == "__eq__"
    assert expr.args[0].op == "Extract" and expr.args[0].args[0] == 6 and expr.args[0].args[1] == 0
    assert expr.args[0].args[2] is a
    assert expr.args[1].args == (0x28, 7)

    expr = claripy.Extract(15, 0, claripy.Concat(claripy.BVV(0, 48), a)) == b
    assert expr is (a == claripy.BVV(0x28, 8))

    bb = claripy.BVV(0x28, 24)
    d = claripy.BVS("d", 8, explicit_name=True)
    expr = claripy.Extract(23, 0, claripy.Concat(claripy.BVV(0, 24), d)) == bb
    assert expr is (d == claripy.BVV(0x28, 8))

    dd = claripy.BVS("dd", 23, explicit_name=True)
    expr = claripy.Extract(23, 0, claripy.Concat(claripy.BVV(0, 2), dd)) == bb
    assert expr is (dd == claripy.BVV(0x28, 23))

    # this was incorrect before
    # claripy issue #201
    expr = claripy.Extract(31, 8, claripy.Concat(claripy.BVV(0, 24), dd)) == claripy.BVV(0xFFFF, 24)
    assert expr is not (dd == claripy.BVV(0xFFFF, 23))


def test_one_xor_exp_eq_zero():
    var1 = claripy.FPV(150, claripy.fp.FSORT_DOUBLE)
    var2 = claripy.FPS("test", claripy.fp.FSORT_DOUBLE)
    result = var1 <= var2
    expr = claripy.BVV(1, 1) ^ (claripy.If(result, claripy.BVV(1, 1), claripy.BVV(0, 1))) == claripy.BVV(0, 1)

    assert expr is result


def test_bitwise_and_if():
    e = claripy.BVS("e", 8)
    cond1 = e >= 5
    cond2 = e != 5
    ifcond1 = claripy.If(cond1, claripy.BVV(1, 1), claripy.BVV(0, 1))
    ifcond2 = claripy.If(cond2, claripy.BVV(1, 1), claripy.BVV(0, 1))
    result = claripy.If(e > 5, claripy.BVV(1, 1), claripy.BVV(0, 1))
    assert ifcond1 & ifcond2 is result


def test_invert_if():
    cond = claripy.BoolS("cond")
    expr = ~(claripy.If(cond, claripy.BVV(1, 1), claripy.BVV(0, 1)))
    result = claripy.If(claripy.Not(cond), claripy.BVV(1, 1), claripy.BVV(0, 1))
    assert expr is result


def test_sub_constant():
    expr = claripy.BVS("expr", 32)
    assert (expr - 5 == 0) is (expr == 5)


def test_extract():
    cond = claripy.BoolS("cond")
    expr = claripy.If(cond, claripy.BVV(1, 32), claripy.BVV(0, 32))[0:0]
    result = claripy.If(cond, claripy.BVV(1, 1), claripy.BVV(0, 1))
    assert expr is result

    e = claripy.BVS("e", 32)
    expr2 = (~e)[0:0]  # pylint:disable=unsubscriptable-object
    result2 = ~(e[0:0])
    assert expr2 is result2


def perf():
    import timeit  # pylint:disable=import-outside-toplevel

    print(
        timeit.timeit(
            "perf_boolean_and_simplification_0()",
            number=10,
            setup="from __main__ import perf_boolean_and_simplification_0",
        )
    )
    print(
        timeit.timeit(
            "perf_boolean_and_simplification_1()",
            number=10,
            setup="from __main__ import perf_boolean_and_simplification_1",
        )
    )


if __name__ == "__main__":
    test_simplification()
    test_bool_simplification()
    test_rotate_shift_mask_simplification()
    test_reverse_extract_reverse_simplification()
    test_reverse_concat_reverse_simplification()
    test_concrete_flatten()
    test_mask_eq_constant()
    test_and_mask_comparing_against_constant_simplifier()
    test_zeroext_extract_comparing_against_constant_simplifier()
    test_one_xor_exp_eq_zero()
    test_bitwise_and_if()
    test_invert_if()
    test_sub_constant()
    test_extract()
