# pylint:disable=missing-class-docstring,no-self-use
import math
import unittest

import claripy


class TestFp(unittest.TestCase):
    def test_nan(self):
        a = claripy.FPS("a", claripy.FSORT_FLOAT)
        b = claripy.BVS("b", 32)

        s1 = claripy.Solver()
        s1.add((a + 1).isNaN())
        res = s1.eval(a, 1)[0]
        assert math.isnan(res)

        s2 = claripy.Solver()
        s2.add(b.raw_to_fp().isNaN())
        res = s2.eval(b, 1)[0]
        assert res & 0xFF800000 == 0x7F800000 and res & 0x007FFFFF != 0

        s3 = claripy.Solver()
        s3.add(a.isNaN())
        res = s3.eval(a.raw_to_bv(), 1)[0]
        assert res & 0xFF800000 == 0x7F800000 and res & 0x007FFFFF != 0

    def test_nan_set(self):
        v0 = claripy.FPV(float("nan"), claripy.FSORT_DOUBLE)
        v1 = claripy.FPV(float("nan"), claripy.FSORT_DOUBLE)

        assert v0 is v1

        # no exception should be raising
        s = {v0}
        s |= {v1}
        assert len(s) == 1

    def test_negative_zero(self):
        """
        Python does not distinguish between +0.0 and -0.0 and thus, claripy returns same AST for both. However, they
        have different bit representations and hence are different.
        """

        zd = claripy.FPV(0.0, claripy.FSORT_DOUBLE)  # pylint: disable=unused-variable
        nzd = claripy.FPV(-0.0, claripy.FSORT_DOUBLE)
        zf = claripy.FPV(0.0, claripy.FSORT_FLOAT)  # pylint: disable=unused-variable
        nzf = claripy.FPV(-0.0, claripy.FSORT_FLOAT)
        s = claripy.Solver()
        assert s.eval(nzd.to_bv(), 1)[0] == 0x8000000000000000
        assert s.eval(nzf.to_bv(), 1)[0] == 0x80000000

    def test_fp_ops(self):
        a = claripy.FPV(1.5, claripy.FSORT_DOUBLE)
        b = claripy.fpToUBV(claripy.fp.RM_NearestTiesEven, a, 32)

        s = claripy.Solver()
        assert s.eval(b, 1)[0] == 2

    def test_fp_precision_loss(self):
        dd = claripy.FPV(101817237862.0, claripy.FSORT_DOUBLE)
        s = claripy.Solver()
        edd = s.eval(dd.to_bv(), 1)[0]
        edd2 = s.eval(dd.to_fp(claripy.FSORT_FLOAT).to_fp(claripy.FSORT_DOUBLE).to_bv(), 1)[0]
        assert edd != edd2
        assert edd2 == 0x4237B4C7C0000000


if __name__ == "__main__":
    unittest.main()
