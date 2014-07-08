import logging
l = logging.getLogger("claripy.abstract_call")
l.setLevel(logging.DEBUG)

class A(object):
    '''
    An A(bstractCall) tracks a tree of calls (including operations) on arguments.
    '''

    def __init__(self, op, args):
        self._op = op
        self._args = args

    def apply(self, backend):
        args = [ ]
        for a in self._args:
            if isinstance(a, A):
                args.append(a.apply(self))
            else:
                args.append(a)

        c = backend.call(self._op, args)
        l.debug("result: %s", c)
        return c

    def __repr__(self):
        if '__' in self._op:
            return "%s.%s%s" % (self._args[0], self._op, self._args[1:])
        else:
            return "%s%s" % (self._op, self._args)
