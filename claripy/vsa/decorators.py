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

        # FIXME: Now we have a very bad assumption - if we see two IfProxy
        # instances as the two operands, we assume they must both be true or
        # false.
        if isinstance(args[0], IfProxy):
            ifproxy = args[0]
            cond = ifproxy.condition
            if len(args) > 1 and isinstance(args[1], IfProxy):
                true_args = (ifproxy.trueexpr, ) + (args[1].trueexpr, ) + args[2:]
                false_args = (ifproxy.falseexpr, ) + (args[1].falseexpr, ) +  args[2:]
            else:
                true_args = (ifproxy.trueexpr, ) + args[1 : ]
                false_args = (ifproxy.falseexpr, ) + args[1 : ]
            trueexpr = f(*true_args, **kwargs)
            falseexpr = f(*false_args, **kwargs)

            return IfProxy(cond, trueexpr, falseexpr)

        if len(args) > 1 and isinstance(args[1], IfProxy):
            ifproxy = args[1]
            cond = ifproxy.condition
            true_args = args[ : 1] + (ifproxy.trueexpr, ) + args[2:]
            false_args = args[ : 1] + (ifproxy.falseexpr, ) + args[2:]
            trueexpr = f(*true_args)
            falseexpr = f(*false_args, **kwargs)

            return IfProxy(cond, trueexpr, falseexpr)

        if len(args) > 2 and isinstance(args[2], IfProxy):
            ifproxy = args[2]
            cond = ifproxy.condition
            true_args = args[: 2] + (ifproxy.trueexpr, ) + args[3:]
            false_args = args[: 2] + (ifproxy.falseexpr, ) + args[3:]
            trueexpr = f(*true_args, **kwargs)
            falseexpr = f(*false_args, **kwargs)

            return IfProxy(cond, trueexpr, falseexpr)

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
        if isinstance(args[0], IfProxy):
            ifproxy = args[0]
            cond = ifproxy.condition
            if len(args) > 1 and isinstance(args[1], IfProxy):
                true_args = (ifproxy.trueexpr, ) + (args[1].trueexpr, ) + args[2:]
                false_args = (ifproxy.falseexpr, ) + (args[1].falseexpr, ) +  args[2:]
            else:
                true_args = (ifproxy.trueexpr, ) + args[1 : ]
                false_args = (ifproxy.falseexpr, ) + args[1 : ]
            trueexpr = f(*true_args, **kwargs)
            falseexpr = f(*false_args, **kwargs)

            return IfProxy(cond, trueexpr, falseexpr)

        if len(args) > 1 and isinstance(args[1], IfProxy):
            ifproxy = args[1]
            cond = ifproxy.condition
            true_args = args[ : 1] + (ifproxy.trueexpr, ) + args[2:]
            false_args = args[ : 1] + (ifproxy.falseexpr, ) + args[2:]
            trueexpr = f(*true_args)
            falseexpr = f(*false_args, **kwargs)

            return IfProxy(cond, trueexpr, falseexpr)

        if len(args) > 2 and isinstance(args[2], IfProxy):
            ifproxy = args[2]
            cond = ifproxy.condition
            true_args = args[: 2] + (ifproxy.trueexpr, ) + args[3:]
            false_args = args[: 2] + (ifproxy.falseexpr, ) + args[3:]
            trueexpr = f(*true_args, **kwargs)
            falseexpr = f(*false_args, **kwargs)

            return IfProxy(cond, trueexpr, falseexpr)

        return f(*args, **kwargs)

    return expander

from .ifproxy import IfProxy