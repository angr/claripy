import nose
import logging
l = logging.getLogger("claripy.test")

import claripy.backends, claripy.expressions

def test_expressions():
    # to and from actual
    a = claripy.expressions.AbstractExpression(op='BitVec', args=('x', 32), variables={'x'}, symbolic=True)
    z = claripy.backends.BackendZ3()
    b = a.actualize(z)
    c = b+b
    nose.tools.assert_equal(str(c), 'ActualExpression(x + x)')
    d = c.abstract().actualize(z)
    nose.tools.assert_true(d.symbolic)
    nose.tools.assert_equal(str(d), str(c))

    # concrete stuff
    #b_c = claripy.backends.BackendConcrete()
    #a = claripy.expressions.AbstractExpression(op='BitVecVal', args=(0, 32), variables=set(), symbolic=False)
    #b = claripy.expressions.AbstractExpression(op='BitVecVal', args=(1, 32), variables=set(), symbolic=False)
    #b = a.actualize(z)
    #c = b+b
    #nose.tools.assert_equal(str(c), 'ActualExpression(x + x)')
    #d = c.abstract().actualize(z)
    #nose.tools.assert_equal(str(d), str(c))

if __name__ == '__main__':
    test_expressions()
    print "WOO"
