import logging
import functools

from .decorators import expand_ifproxy

l = logging.getLogger('claripy.vsa.ifproxy')

def proxified(f):
    @functools.wraps(f)
    def expander(self, o):
        '''
        :param args: All arguments
        :return:
        '''
        op_name = f.__name__
        args = [self.trueexpr, self.falseexpr]
        ret = []
        for arg in args:
            obj = NotImplemented

            # first, try the operation with the first guy
            if hasattr(arg, op_name):
                op = getattr(arg, op_name)
                obj = op(o)
            # now try the reverse operation with the second guy
            if obj is NotImplemented and hasattr(o, op_name):
                op = getattr(o, opposites[op_name])
                obj = op(arg)

            if obj is NotImplemented:
                l.error("%s neither %s nor %s apply in IfProxy.expander()", self, op_name, opposites[op_name])
                raise BackendError("unable to apply operation on provided converted")

            ret.append(obj)

        return IfProxy(self.condition, ret[0], ret[1])

    return expander

class IfProxy(object):
    def __init__(self, cond, true_expr, false_expr):
        self._cond = cond
        self._true = true_expr
        self._false = false_expr

    @property
    def condition(self):
        return self._cond

    @property
    def trueexpr(self):
        return self._true

    @property
    def falseexpr(self):
        return self._false

    def __len__(self):
        return len(self._true)

    def __repr__(self):
        return 'IfProxy(%s, %s, %s)' % (self._cond, self._true, self._false)

    @proxified
    def __eq__(self, other): pass

    @proxified
    def __ne__(self, other): pass

    @proxified
    def __or__(self, other): pass

    @proxified
    def __xor__(self, other): pass

    @proxified
    def __rxor__(self, other): pass

    @proxified
    def __and__(self, other): pass

    @proxified
    def __rand__(self, other): pass

from ..errors import BackendError
from ..operations import opposites