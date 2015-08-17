import logging
import functools

from .decorators import expand_ifproxy
from ..backend_object import BackendObject

l = logging.getLogger('claripy.vsa.ifproxy')

def proxified(f):
    @functools.wraps(f)
    def expander(self, *args):
        '''
        :param args: All arguments
        :return:
        '''
        op_name = f.__name__
        if_exprs = [ self.trueexpr, self.falseexpr ]
        ret = [ ]

        if isinstance(args[0], IfProxy):
            # Are the conditions opposite?
            other = args[0]
            cond1 = self.condition
            cond2 = other.condition

            if cond1.op in inverse_operations and \
                    inverse_operations[cond1.op] == cond2.op and \
                    all([ BoolResult.is_true(a1.identical(a2)) for a1, a2 in zip(cond1.args, cond2.args)]):
                other_args = [ other.falseexpr, other.trueexpr ]
            else:
                # FIXME: We are assuming the conditions are the same with self.condition...
                other_args = [ other.trueexpr, other.falseexpr ]
        else:
            other_args = [ args[0], args[0]  ]

        for i, arg in enumerate(if_exprs):
            if len(args) == 0:
                obj = NotImplemented

                if hasattr(arg, op_name):
                    op = getattr(arg, op_name)
                    obj = op()

                if obj is NotImplemented:
                    l.error('%s %s doesn\'t apply in IfProxy.expander()', self, op_name)
                    raise BackendError('Unable to apply operation on provided arguments.')

            else:
                obj = NotImplemented
                o = other_args[i]

                # first, try the operation with the first guy
                if hasattr(arg, op_name):
                    op = getattr(arg, op_name)
                    obj = op(o)
                # now try the reverse operation with the second guy
                if obj is NotImplemented and hasattr(o, opposites[op_name]):
                    op = getattr(o, opposites[op_name])
                    obj = op(arg)

                if obj is NotImplemented:
                    l.error("%s neither %s nor %s apply in IfProxy.expander()", self, op_name, opposites[op_name])
                    raise BackendError("unable to apply operation on provided arguments.")

                ret.append(obj)

        return IfProxy(self.condition, ret[0], ret[1])

    return expander

class IfProxy(BackendObject):
    def __init__(self, cond, true_expr, false_expr):
        self._cond = cond
        self._true = true_expr
        self._false = false_expr

    @staticmethod
    def unwrap(ifproxy, side=True):
        '''

        :param ifproxy:
        :param side: Decides which expr you want
        :return: A tuple of condition and expr
        '''

        # FIXME: find a better way to deal with cross-or'ed conditions!
        if isinstance(ifproxy, IfProxy):
            if side:
                return ifproxy.condition, IfProxy.unwrap(ifproxy.trueexpr, side)[1]
            else:
                return ifproxy.condition, IfProxy.unwrap(ifproxy.falseexpr, side)[1]
        else:
            return None, ifproxy

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

    def identical(self, o):
        return self._true.identical(o._true) and self._false.identical(o._false) and self._cond.identical(o._cond)

    @proxified
    def __eq__(self, other): pass

    @proxified
    def __ne__(self, other): pass

    @proxified
    def __neg__(self): pass

    @proxified
    def __add__(self, other): pass

    @proxified
    def __radd__(self, other): pass

    @proxified
    def __sub__(self, other): pass

    @proxified
    def __rsub__(self, other): pass

    def __invert__(self):
        return IfProxy(self.condition, self.trueexpr.__invert__(), self.falseexpr.__invert__())

    @proxified
    def __or__(self, other): pass

    @proxified
    def __ror__(self, other): pass

    @proxified
    def __xor__(self, other): pass

    @proxified
    def __rxor__(self, other): pass

    @proxified
    def __and__(self, other): pass

    @proxified
    def __rand__(self, other): pass

from ..errors import BackendError
from ..operations import opposites, inverse_operations
from .bool_result import BoolResult
