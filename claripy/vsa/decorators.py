import functools

def expand_ifproxy(f):
    @functools.wraps(f)
    def expander(*args, **kwargs):
        '''
        For each IfProxy proxified argument, we expand it so that it is
        converted into two operands (true expr and false expr, respectively).
        After the operation, we rewrap the two sides together in a new
        IfProxy with the old cond.

        :param args: All arguments
        :return:
        '''

        # FIXME: Now we have a very bad assumption - if we see more than one IfProxy
        # instances as the two operands, we assume they must both be true or
        # false.
        any_ifproxy = any([isinstance(a, IfProxy) for a in args])
        if any_ifproxy:
            true_args = None
            false_args = None
            cond = None
            # build true_args and false_args
            for a in args:
                cond = a.condition if isinstance(a, IfProxy) and cond is None else cond
                this_true_arg = IfProxy.unwrap(a, True)[1] if isinstance(a, IfProxy) else a
                this_false_arg = IfProxy.unwrap(a, False)[1] if isinstance(a, IfProxy) else a
                true_args = (this_true_arg, ) if true_args is None else true_args + (this_true_arg, )
                false_args = (this_false_arg, ) if false_args is None else false_args + (this_false_arg, )

            trueexpr = f(*true_args, **kwargs)
            falseexpr = f(*false_args, **kwargs)

            return IfProxy(cond, trueexpr, falseexpr)

        else:
            return f(*args, **kwargs)

    return expander

def expr_op_expand_ifproxy(f):
    @functools.wraps(f)
    def expander(self, *args, **kwargs):
        '''
        For each IfProxy proxified argument, we expand it so that it is
        converted into two operands (true expr and false expr, respectively).
        After the operation, we rewrap the two sides together in a new
        IfProxy with the old cond.

        :param args: All arguments
        :return:
        '''

        # FIXME: Now we have a very bad assumption - if we see two IfProxy
        # instances as the two operands, we assume they must both be true or
        # false.
        any_ifproxy = any([isinstance(a, Base) and isinstance(a.model, IfProxy) for a in args])
        if any_ifproxy:
            true_args = None
            false_args = None
            cond = None
            # build true_args and false_args
            for a in args:
                ifproxy = a.model if isinstance(a, Base) and isinstance(a.model, IfProxy) else None
                cond = ifproxy.condition if ifproxy is not None and cond is None else cond
                this_true_arg = IfProxy.unwrap(ifproxy, True)[1] if ifproxy is not None else a.model
                this_false_arg = IfProxy.unwrap(ifproxy, False)[1] if ifproxy is not None else a.model
                true_args = (this_true_arg, ) if true_args is None else true_args + (this_true_arg, )
                false_args = (this_false_arg, ) if false_args is None else false_args + (this_false_arg, )

            trueexpr = f(self, *true_args, **kwargs)
            falseexpr = f(self, *false_args, **kwargs)

            return IfProxy(cond, trueexpr, falseexpr)

        else:
            return f(self, *args, **kwargs)

    return expander

from .ifproxy import IfProxy
from ..ast.base import Base
