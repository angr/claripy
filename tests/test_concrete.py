# pylint: disable=missing-class-docstring,no-self-use
from __future__ import annotations

import unittest

import claripy


class TestConcreteBackend(unittest.TestCase):
    def test_concrete(self):
        a = claripy.BVV(10, 32)
        b = claripy.BoolV(True)

        assert isinstance(claripy.backends.concrete.convert(a), claripy.bv.BVV)
        assert isinstance(claripy.backends.concrete.convert(b), bool)

        a = claripy.BVV(1337, 32)
        b = a[31:16]
        c = claripy.BVV(0, 16)
        assert b is c

        bc = claripy.backends.concrete
        d = claripy.BVV(-1, 32)
        assert bc.convert(d) == 0xFFFFFFFF

        e = claripy.BVV(2**32 + 1337, 32)
        assert bc.convert(e) == 1337

    def test_concrete_fp(self):
        f = claripy.FPV(1.0, claripy.FSORT_FLOAT)
        assert claripy.backends.concrete.eval(f, 2) == (1.0,)


if __name__ == "__main__":
    unittest.main()
