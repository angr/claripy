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

if __name__ == '__main__':
    test_simplification()
    test_bool_simplification()
