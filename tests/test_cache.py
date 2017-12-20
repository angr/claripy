import sys

import claripy
import nose


def test_exhausted():
    a = claripy.BVS('a', 64)
    s = claripy.SolverComposite()

    for i in range(len(a) / 8):
        tmp = a[8 * (i + 1) - 1:8 * i]
        v1 = s.eval(tmp, 260)
        v2 = s.eval(tmp, 260)
        nose.tools.assert_equal(v1, v2)
        nose.tools.assert_equal(len(v2), 256)

        s.add(claripy.ULE(tmp, 250))
        m1 = s.max(tmp)
        m2 = s.max(tmp)
        nose.tools.assert_equal(m1, m2)
        nose.tools.assert_equal(m2, 250)

        s.add(claripy.UGT(tmp, 5))
        m1 = s.min(tmp)
        m2 = s.min(tmp)
        nose.tools.assert_equal(m1, m2)
        nose.tools.assert_equal(m2, 6)


if __name__ == '__main__':
    if len(sys.argv) > 1:
        globals()['test_' + sys.argv[1]]()

    else:
        for func_name, func in globals().items():
            if func_name.startswith('test_') and hasattr(func, '__call__'):
                func()
