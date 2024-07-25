# pylint: disable=missing-class-docstring,no-self-use
from __future__ import annotations

import unittest

from claripy.vsa import StridedInterval


def check_si_fields(si, stride, lb, ub):
    if si.stride != stride:
        return False
    if si.lower_bound != lb:
        return False
    return si.upper_bound == ub


class TestStridedInterval(unittest.TestCase):
    def test_smart_join(self):
        s1 = StridedInterval(bits=4, stride=3, lower_bound=9, upper_bound=12)
        s2 = StridedInterval(bits=4, stride=3, lower_bound=0, upper_bound=3)
        j = StridedInterval.pseudo_join(s1, s2)
        u = StridedInterval.least_upper_bound(s1, s2)
        assert check_si_fields(u, 3, 0, 12)
        assert check_si_fields(j, 3, 0, 12)

        s1 = StridedInterval(bits=4, stride=0, lower_bound=8, upper_bound=8)
        s2 = StridedInterval(bits=4, stride=1, lower_bound=14, upper_bound=15)
        s3 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=4)
        u = StridedInterval.least_upper_bound(s1, s2, s3)
        assert check_si_fields(u, 1, 14, 8)

        s1 = StridedInterval(bits=4, stride=3, lower_bound=2, upper_bound=8)
        s2 = StridedInterval(bits=4, stride=0, lower_bound=1, upper_bound=1)
        j = StridedInterval.pseudo_join(s1, s2)
        u = StridedInterval.least_upper_bound(s1, s2)
        assert check_si_fields(u, 3, 2, 1)
        assert check_si_fields(j, 3, 2, 1)


if __name__ == "__main__":
    unittest.main()
