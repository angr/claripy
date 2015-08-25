import claripy
import nose

def test_simplification():
    def assert_identical(a, b):
        nose.tools.assert_true(a.identical(b))

    x, y, z = (claripy.BV(name, 32) for name in ('x', 'y', 'z'))

    # test extraction of concatted values
    concatted = claripy.Concat(x, y, z)

    assert_identical(concatted[95:64].reduced, x)
    assert_identical(concatted[63:32].reduced, y)
    assert_identical(concatted[31:0].reduced, z)

    assert_identical(concatted[95:32].reduced, claripy.Concat(x, y))
    assert_identical(concatted[63:0].reduced, claripy.Concat(y, z))

    assert_identical(concatted[95:0].reduced, concatted)

    assert_identical(concatted[47:0].reduced, claripy.Concat(y, z)[47:0])
    assert_identical(concatted[70:0].reduced, concatted[70:0])
    assert_identical(concatted[70:15].reduced, concatted[70:15])
    assert_identical(concatted[70:35].reduced, claripy.Concat(x, y)[38:3])

    # make sure the division simplification works
    assert_identical(2+x, claripy._backends['BackendZ3'].simplify(1+x+1))
    assert_identical(x/y, claripy._backends['BackendZ3'].simplify(x/y))
    assert_identical(x%y, claripy._backends['BackendZ3'].simplify(x%y))

if __name__ == '__main__':
    test_simplification()
