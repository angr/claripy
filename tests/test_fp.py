import claripy
import math

def test_nan():
    a = claripy.FPS('a', claripy.FSORT_FLOAT)
    b = claripy.BVS('b', 32)

    s1 = claripy.Solver()
    s1.add((a + 1).isNaN())
    res = s1.eval(a, 1)[0]
    assert math.isnan(res)

    s2 = claripy.Solver()
    s2.add(b.raw_to_fp().isNaN())
    res = s2.eval(b, 1)[0]
    assert res & 0xff800000 == 0x7f800000 and res & 0x007fffff != 0

    s3 = claripy.Solver()
    s3.add(a.isNaN())
    res = s3.eval(a.raw_to_bv(), 1)[0]
    assert res & 0xff800000 == 0x7f800000 and res & 0x007fffff != 0

def test_fp_ops():
    a = claripy.FPV(1.5, claripy.FSORT_DOUBLE)
    b = claripy.fpToUBV(claripy.fp.RM_NearestTiesEven, a, 32)

    s = claripy.Solver()
    assert s.eval(b, 1)[0] == 2

if __name__ == '__main__':
    test_fp_ops()
    test_nan()