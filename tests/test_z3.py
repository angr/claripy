# pylint: disable=missing-class-docstring,no-self-use
from __future__ import annotations

import sys
import unittest

import claripy
from claripy import FPS, fpToSBV, fpToUBV
from claripy.fp import RM


class TestZ3(unittest.TestCase):
    """
    A class used for testing z3
    """

    def test_extrema(self):
        """
        Test the _extrema function within the z3 backend
        """
        z = claripy.backends.z3

        s = z.solver()
        x = claripy.BVS("x", 8)
        range_ = (0, 2**x.length - 1)

        assert z.min(x, solver=s) == range_[0]
        assert z.max(x, solver=s) == range_[1]

        for i in range(0, range_[1] + 1, 10):
            # ==
            assert z.min(x, solver=s, extra_constraints=(x == i,)) == i
            assert z.max(x, solver=s, extra_constraints=(x == i,)) == i
            # <=
            assert z.min(x, solver=s, extra_constraints=(x <= i,)) == range_[0]
            assert z.max(x, solver=s, extra_constraints=(x <= i,)) == i
            # >=
            assert z.min(x, solver=s, extra_constraints=(x >= i,)) == i
            assert z.max(x, solver=s, extra_constraints=(x >= i,)) == range_[1]

    def test_str2int(self):
        """
        Test the str_to_int_unlimited function.
        """

        s2i = claripy.backends.backend_z3.str_to_int_unlimited
        CHUNK_SIZE = sys.get_int_max_str_digits() if hasattr(sys, "get_int_max_str_digits") else 640

        assert s2i("0") == 0
        assert s2i("1337") == 1337
        assert s2i("1337133713371337") == 1337133713371337
        assert s2i("1" + "0" * 639) == 10**639
        assert s2i("1" + "0" * 640) == 10**640
        assert s2i("1" + "0" * 641) == 10**641
        assert s2i("1" + "0" * 640 + "1") == 10**641 + 1
        assert s2i("1" + "0" * 8192) == 10**8192

        assert s2i("1" + "0" * (CHUNK_SIZE - 1)) == 10 ** (CHUNK_SIZE - 1)
        assert s2i("1" + "0" * CHUNK_SIZE) == 10**CHUNK_SIZE
        assert s2i("1" + "0" * (CHUNK_SIZE + 1)) == 10 ** (CHUNK_SIZE + 1)

        assert s2i("-0") == 0
        assert s2i("-1") == -1
        assert s2i("-1" + "0" * CHUNK_SIZE) == -(10**CHUNK_SIZE)

    def test_int2str(self):
        """
        Test the int_to_str_unlimited function.
        """

        i2s = claripy.backends.backend_z3.int_to_str_unlimited
        CHUNK_SIZE = sys.get_int_max_str_digits() if hasattr(sys, "get_int_max_str_digits") else 640

        assert i2s(0) == "0"
        assert i2s(-1) == "-1"
        assert i2s(1337) == "1337"
        assert i2s(10**8192) == "1" + "0" * 8192
        assert i2s(10**CHUNK_SIZE) == "1" + "0" * CHUNK_SIZE

    def test_get_long_strings(self):
        # Python 3.11 introduced limits in decimal-to-int conversion. we bypass it by using the str_to_int_unlimited
        # method.
        z3 = claripy.backends.backend_z3

        s = claripy.backends.z3.solver()
        backend = z3.BackendZ3()
        x = claripy.BVS("x", 16385 * 8)
        backend.add(s, [x == 10**16384])
        d = backend.eval(x, 1, solver=s)
        assert d == [10**16384]

    def test_abstract_sbv(self):
        """
        Test abstracting fpToSBV
        """

        f = FPS("f", claripy.FSORT_FLOAT)
        sbv = fpToSBV(RM.RM_NearestTiesEven, f, 32)

        sbv2 = claripy.backends.z3.simplify(sbv)
        assert sbv2.length == 32

    def test_abstract_ubv(self):
        """
        Test abstracting fpToUBV
        """

        f = FPS("f", claripy.FSORT_FLOAT)
        sbv = fpToUBV(RM.RM_NearestTiesEven, f, 32)

        sbv2 = claripy.backends.z3.simplify(sbv)
        assert sbv2.length == 32


if __name__ == "__main__":
    unittest.main()
