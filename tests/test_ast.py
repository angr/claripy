import nose.tools

import claripy


def test_lite_repr():
    one = claripy.BVV(1, 8)
    two = claripy.BVV(2, 8)
    a = claripy.BVS('a', 8)
    b = claripy.BVS('b', 8)

    nose.tools.assert_regex((a + one * b + two).shallow_repr(),
                            r'\<BV8 __add__\(a_\d+_8, \(1 \* b_\d+_8\), 2\)\>')
    nose.tools.assert_regex(((a + one) * (b + two)).shallow_repr(),
                            r'\<BV8 \(a_\d+_8 \+ 1\) \* \(b_\d+_8 \+ 2\)\>')
    nose.tools.assert_regex((a * one + b * two).shallow_repr(),
                            r'\<BV8 \(a_\d+_8 \* 1\) \+ \(b_\d+_8 \* 2\)\>')
    #r'\<BV8 a_\d+_8 \* 1 \+ b_\d+_8 \* 2\>')
    nose.tools.assert_regex(((one + a)*(two + b)+(two + a)*(one + b)).shallow_repr(),
                            r'\<BV8 \(\(1 \+ a_\d+_8\) \* \(2 \+ b_\d+_8\)\) \+ \(\(2 \+ a_\d+_8\) \* \(1 \+ b_\d+_8\)\)\>')



if __name__ == '__main__':
    test_lite_repr()
