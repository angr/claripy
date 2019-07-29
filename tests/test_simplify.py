import claripy
import nose

def test_bool_simplification():
    def assert_correct(a, b):
        nose.tools.assert_true(claripy.backends.z3.identical(claripy.simplify(a), b))

    a, b, c = (claripy.BoolS(name) for name in ('a', 'b', 'c'))

    assert_correct(claripy.And(a, claripy.Not(a)), claripy.false)
    assert_correct(claripy.Or(a, claripy.Not(a)), claripy.true)

    complex_true_expression = claripy.Or(
        claripy.And(a,b),
        claripy.Or(claripy.And(a, claripy.Not(b)), claripy.And(claripy.Not(a), c)),
        claripy.Or(claripy.And(a, claripy.Not(b)), claripy.And(claripy.Not(a), claripy.Not(c))))
    assert_correct(complex_true_expression, claripy.true)

def test_simplification():
    def assert_correct(a, b):
        nose.tools.assert_true(claripy.backends.z3.identical(a, b))

    x, y, z = (claripy.BVS(name, 32) for name in ('x', 'y', 'z'))

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

    # make sure the division simplification works
    assert_correct(2+x, claripy.backends.z3.simplify(1+x+1))
    assert_correct(x/y, claripy.backends.z3.simplify(x/y))
    assert_correct(x%y, claripy.backends.z3.simplify(x%y))


def test_rotate_shift_mask_simplification():

    a = claripy.BVS('N', 32, max=0xc, min=0x1)
    extend_ = claripy.BVS('extend', 32, uninitialized=True)
    a_ext = extend_.concat(a)
    expr = ((a_ext << 3) | (claripy.LShR(a_ext, 61))) & 0x7fffffff8
    # print(expr)
    # print(expr._model_vsa)
    model_vsa = expr._model_vsa
    nose.tools.assert_equal(model_vsa.lower_bound, 8)
    nose.tools.assert_equal(model_vsa.upper_bound, 0x60)
    nose.tools.assert_equal(model_vsa.cardinality, 12)


def test_reverse_extract_reverse_simplification():

    # without the reverse_extract_reverse simplifier, loading dx from rdx will result in the following complicated
    # expression:
    #   Reverse(Extract(63, 48, Reverse(BVS('rdx', 64))))

    a = claripy.BVS('rdx', 64)
    dx = claripy.Reverse(claripy.Extract(63, 48, claripy.Reverse(a)))

    # simplification should have kicked in at this moment
    nose.tools.assert_equal(dx.op, 'Extract')
    nose.tools.assert_equal(dx.args[0], 15)
    nose.tools.assert_equal(dx.args[1], 0)
    nose.tools.assert_is(dx.args[2], a)


def test_reverse_concat_reverse_simplification():

    # Reverse(Concat(Reverse(a), Reverse(b))) = Concat(b, a)

    a = claripy.BVS('a', 32)
    b = claripy.BVS('b', 32)
    x = claripy.Reverse(claripy.Concat(claripy.Reverse(a), claripy.Reverse(b)))

    nose.tools.assert_equal(x.op, 'Concat')
    nose.tools.assert_is(x.args[0], b)
    nose.tools.assert_is(x.args[1], a)


def perf_boolean_and_simplification_0():
    # Create a gigantic And AST with many operands, one variable at a time
    bool_vars = [ claripy.BoolS("b%d" % i) for i in range(1500) ]
    v = bool_vars[0]
    for i in range(1, len(bool_vars)):
        v = claripy.And(v, bool_vars[i])


def perf_boolean_and_simplification_1():
    # Create a gigantic And AST with many operands, many variables at a time
    bool_vars = [ claripy.BoolS("b%d" % i) for i in range(500) ]
    v = bool_vars[0]
    for i in range(1, len(bool_vars)):
        if v.op == "And":
            v = claripy.And(*(v.args + (bool_vars[i] == False,)))  # pylint:disable=singleton-comparison
        else:
            v = claripy.And(v, bool_vars[i])

def test_concrete_flatten():
    a = claripy.BVS('a', 32)
    b = a + 10
    c = 10 + b
    d = a + 20
    nose.tools.assert_is(c, d)

    # to future test writers or debuggers: whether the answer is b_neg or b is not particularly important
    e = a - 10
    f = e + 20
    b_neg = a - -10
    nose.tools.assert_is(f, b_neg)

    g = e - 10
    h = a - 20
    nose.tools.assert_is(g, h)

    i = d - 10
    nose.tools.assert_is(i, b)

def perf():
    import timeit
    print(timeit.timeit("perf_boolean_and_simplification_0()",
                        number=10,
                        setup="from __main__ import perf_boolean_and_simplification_0"))
    print(timeit.timeit("perf_boolean_and_simplification_1()",
                        number=10,
                        setup="from __main__ import perf_boolean_and_simplification_1"))


if __name__ == '__main__':
    test_simplification()
    test_bool_simplification()
    test_rotate_shift_mask_simplification()
    test_reverse_extract_reverse_simplification()
    test_reverse_concat_reverse_simplification()
    test_concrete_flatten()
