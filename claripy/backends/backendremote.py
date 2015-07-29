import cPickle as pickle
import time

from .solver_backend import SolverBackend
from .backend_z3 import BackendZ3
from . import remotetasks

class TrackingSolver(object):
    def __init__(self, sz3):
        self.sz3 = sz3
        self.constraints = []

    def plus_extra(self, extra_constraints):
        return self.constraints + list(extra_constraints)


def get(res):
    before = time.time()
    result = res.get(interval=0.02)
    # print "task took %f" % (time.time() - before)
    return result

class BackendRemote(SolverBackend):
    def __init__(self, host='localhost', port=1337, local_timeout=-1):
        super(BackendRemote, self).__init__()
        self.bz3 = BackendZ3()
        self.local_timeout = local_timeout

    def set_claripy_object(self, clrp):
        super(BackendRemote, self).set_claripy_object(clrp)
        self.bz3.set_claripy_object(clrp)

    def solver(self, timeout=None):
        timeout = self.local_timeout if timeout is None else min(self.local_timeout, timeout)
        return TrackingSolver(self.bz3.solver(timeout=timeout))

    def _abstract(self, e):
        return e

    def _convert(self, e):
        return e

    def call(self, ast, result=None):
        return ast

    def _add(self, s, c):
        s.constraints.extend(c)
        self.bz3.add(s.sz3, c)

    def _check(self, s, extra_constraints=()):
        for x in s.plus_extra(extra_constraints):
            if hasattr(x, 'make_uuid'):
                x.make_uuid()
        # print pickle.dumps(s.plus_extra(extra_constraints))
        res = remotetasks.check.delay(s.plus_extra(extra_constraints))
        return get(res)

    def _eval(self, s, expr, n, extra_constraints=(), result=None):
        for x in s.plus_extra(extra_constraints):
            if hasattr(x, 'make_uuid'):
                x.make_uuid()
        # print pickle.dumps(s.plus_extra(extra_constraints))
        res = remotetasks.eval.delay(s.plus_extra(extra_constraints), expr, n)
        return get(res)

    def _results(self, s, extra_constraints=(), generic_model=True):
        for x in s.plus_extra(extra_constraints):
            if hasattr(x, 'make_uuid'):
                x.make_uuid()
        # print pickle.dumps(s.plus_extra(extra_constraints))
        res = remotetasks.results.delay(s.plus_extra(extra_constraints))
        return get(res)

    def _min(self, s, expr, extra_constraints=(), result=None):
        for x in s.plus_extra(extra_constraints):
            if hasattr(x, 'make_uuid'):
                x.make_uuid()
        # print pickle.dumps(s.plus_extra(extra_constraints))
        res = remotetasks.min.delay(s.plus_extra(extra_constraints), expr)
        return get(res)

    def _max(self, s, expr, extra_constraints=(), result=None):
        for x in s.plus_extra(extra_constraints):
            if hasattr(x, 'make_uuid'):
                x.make_uuid()
        # print pickle.dumps(s.plus_extra(extra_constraints))
        res = remotetasks.max.delay(s.plus_extra(extra_constraints), expr)
        return get(res)

    def _size(self, o, result=None):
        return o.length

    def _name(self, o, result=None):
        raise Exception('wat')

    def _identical(a, b, result=None):
        return a.identical(b)
