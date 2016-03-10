import logging

from claripy.vsa import StridedInterval

l = logging.getLogger("angr_tests")

def test_smart_join():
    s1 = StridedInterval(bits=4, stride=3, lower_bound=9, upper_bound=12)
    s2 = StridedInterval(bits=4, stride=3, lower_bound=0, upper_bound=3)
    j = StridedInterval.pseudo_join(s1, s2)
    u = StridedInterval.least_upper_bound(s1, s2)
    assert str(u) == "<4>0x3[0x0, 0xc]"
    assert str(j) == "<4>0x3[0x0, 0xc]"

    s1 = StridedInterval(bits=4, stride=0, lower_bound=8, upper_bound=8)
    s2 = StridedInterval(bits=4, stride=1, lower_bound=14, upper_bound=15)
    s3 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=4)
    u = StridedInterval.least_upper_bound(s1, s2, s3)
    assert str(u) == "<4>0x1[0xe, 0x8]"

    s1 = StridedInterval(bits=4, stride=3, lower_bound=2, upper_bound=8)
    s2 = StridedInterval(bits=4, stride=0, lower_bound=1, upper_bound=1)
    j = StridedInterval.pseudo_join(s1, s2)
    u = StridedInterval.least_upper_bound(s1, s2)
    assert str(u) == "<4>0x3[0x2, 0x1]"
    assert str(j) == "<4>0x3[0x2, 0x1]"


if __name__ == "__main__":
    test_smart_join()