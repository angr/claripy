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
        print len(v1), len(v2)
       #nose.tools.assert_equal(v1, v2)


if __name__ == '__main__':
    if len(sys.argv) > 1:
        globals()['test_' + sys.argv[1]]()

    else:
        for func_name, func in globals().items():
            if func_name.startswith('test_') and hasattr(func, '__call__'):
                func()
