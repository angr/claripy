
import sys

import nose.tools

from claripy.bv import BVV, Extract, SignExt, ZeroExt, Concat, SDiv
from claripy.errors import ClaripyTypeError

def test_bv():
    a = BVV(1, 8)
    b = BVV(2, 8)
    assert a | b == 3
    assert a & b == 0
    assert a / b == 0
    assert b * b == 4
    assert a.signed == a.value
    assert a + 8 == 9

    c = BVV(128, 8)
    assert c.signed == -128

    d = BVV(255, 8)
    assert Extract(1, 0, d) == 3
    assert SignExt(8, d).value == 2**16-1
    assert ZeroExt(8, d).size() == 16
    assert ZeroExt(8, d).value == 255

    e = BVV(0b1010, 4)
    f = BVV(0b11, 2)
    assert Concat(e, e, e, e) == 0b1010101010101010
    assert Concat(e,f,f) == 0b10101111

    # test that __div__ is unsigned
    assert BVV(5, 8) / BVV(254, 8) == 0
    assert SDiv(BVV(5, 8), BVV(-2, 8)) == -2

    zero = BVV(0, 8)

    assert -a == 255
    assert ~a == 254
    assert -zero == 0
    assert ~zero == 255


def test_zero_length():
    a = BVV(1, 8)
    b = BVV(0, 0)
    assert Concat(a, b) == 1
    assert b == b

    nose.tools.assert_raises(ClaripyTypeError, lambda: a + b)
    nose.tools.assert_raises(ClaripyTypeError, lambda: a - b)
    nose.tools.assert_raises(ClaripyTypeError, lambda: a * b)
    nose.tools.assert_raises(ClaripyTypeError, lambda: a / b)

if __name__ == '__main__':

    if len(sys.argv) > 1:
        globals()["test_" + sys.argv[1]]()

    else:
        g = globals().copy()
        for func_name, func in g.iteritems():
            if func_name.startswith("test_") and hasattr(func, "__call__"):
                func()
