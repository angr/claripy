# pylint: disable=missing-class-docstring,no-self-use
from __future__ import annotations

import unittest

import claripy
from claripy.bv import BVV, Concat, Extract, SDiv, SignExt, ZeroExt
from claripy.errors import ClaripyTypeError, ClaripyValueError, ClaripyZeroDivisionError


class TestBv(unittest.TestCase):
    def test_bv(self):
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
        assert SignExt(8, d).value == 2**16 - 1
        assert ZeroExt(8, d).size() == 16
        assert ZeroExt(8, d).value == 255

        e = BVV(0b1010, 4)
        f = BVV(0b11, 2)
        assert Concat(e, e, e, e) == 0b1010101010101010
        assert Concat(e, f, f) == 0b10101111

        # test that __truediv__ is unsigned
        assert BVV(5, 8) / BVV(254, 8) == 0
        assert SDiv(BVV(5, 8), BVV(-2, 8)) == -2

        zero = BVV(0, 8)

        assert -a == 255
        assert ~a == 254
        assert -zero == 0
        assert ~zero == 255

    def test_none_value(self):
        a = claripy.ast.bv.TSI(8)
        b = claripy.ast.bv.BVV(1, 8)
        a.union(b)
        # If we get to this point, the test passed

    def test_get_byte(self):
        a = claripy.BVV(0xABCDEF12, 32)
        assert a.get_byte(0).args[0] == 0xAB
        assert a.get_byte(1).args[0] == 0xCD

        try:
            assert a.get_byte(4).args[0]
        except ValueError:
            pass
        else:
            assert False, "get_byte(4) did not raise an exception"

        b = claripy.BVV(0x1, 2)
        assert b.get_byte(0).args[0] == 0x1
        assert b.get_byte(0).args[1] == 8

    def test_get_bytes(self):
        a = claripy.BVV(0xABCDEF12, 32)
        assert a.get_bytes(0, 1).args[0] == 0xAB
        assert a.get_bytes(0, 2).args[0] == 0xABCD

        assert a.get_bytes(1, 1).args[0] == 0xCD

        try:
            assert a.get_bytes(4, 1).args[0]
        except ValueError:
            pass
        else:
            assert False, "get_bytes(4, 1) did not raise an exception"

        assert a.get_bytes(0, 0).args[0] == 0
        assert a.get_bytes(0, 0).args[1] == 0

        b = claripy.BVV(0x3F0, 10)
        assert b.get_bytes(0, 1).args[0] == 0x3
        assert b.get_bytes(0, 1).args[1] == 8
        assert b.get_bytes(0, 2).args[0] == 0x3F0
        assert b.get_bytes(0, 2).args[1] == 16
        assert b.get_bytes(1, 1).args[0] == 0xF0
        assert b.get_bytes(1, 1).args[1] == 8

    def test_zero_length(self):
        a = BVV(1, 8)
        b = BVV(0, 0)
        assert Concat(a, b) == 1

        self.assertRaises(ClaripyTypeError, lambda: a + b)
        self.assertRaises(ClaripyTypeError, lambda: a - b)
        self.assertRaises(ClaripyTypeError, lambda: a * b)
        self.assertRaises(ClaripyTypeError, lambda: a / b)

    def test_zero_division_errors(self):
        a = BVV(1, 32)
        b = BVV(0, 32)

        def _check_exception(va, vb, op):
            try:
                if hasattr(va, op):
                    getattr(va, op)(vb)
                elif hasattr(claripy, op):
                    getattr(claripy, op)(va, vb)
                else:
                    raise Exception(f"Operation {op} does not exist.")
                raise Exception("The expected exception is not raised.")
            except Exception as ex:  # pylint:disable=broad-except
                assert type(ex) is ClaripyZeroDivisionError

        _check_exception(a, b, "__truediv__")
        _check_exception(a, b, "__floordiv__")
        _check_exception(a, b, "__mod__")
        _check_exception(b, a, "__rtruediv__")
        _check_exception(b, a, "__rfloordiv__")
        _check_exception(b, a, "__rmod__")
        _check_exception(a, b, "SMod")
        _check_exception(a, b, "SDiv")

    def test_type_errors(self):
        self.assertRaises(TypeError, lambda: claripy.BVV(None))
        self.assertRaises(TypeError, lambda: claripy.BVV(3))
        self.assertRaises(TypeError, lambda: claripy.BVV(1.2))
        self.assertRaises(TypeError, lambda: claripy.BVV(b"asdf", b"qwer"))
        self.assertRaises(ClaripyValueError, lambda: claripy.BVV(b"asdf", 8))

        self.assertRaises(TypeError, lambda: claripy.BVS(None, None))
        self.assertRaises(TypeError, lambda: claripy.BVS(None, 3))
        self.assertRaises(TypeError, lambda: claripy.BVS(3, 3))
        self.assertRaises(TypeError, lambda: claripy.BVS(3, None))
        self.assertRaises(TypeError, lambda: claripy.BVS("asdf", None))


if __name__ == "__main__":
    unittest.main()
