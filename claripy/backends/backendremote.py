#import time

from .backend import Backend
from .backend_z3 import BackendZ3
try:
    from . import remotetasks
except ImportError:
    remotetasks = None

class TrackingSolver:
    def __init__(self, sz3):
        self.sz3 = sz3
        self.constraints = []

    def plus_extra(self, extra_constraints):
        return self.constraints + list(extra_constraints)


def get(res):
    #before = time.time()
    result = res.get(interval=0.02)
    # print("task took %f" % (time.time() - before))
    return result

class BackendRemote(Backend):
    def __init__(self, host='localhost', port=1337, local_timeout=-1):
        if remotetasks is None:
            raise ImportError("celery/pymongo is required for BackendRemote")

        super(BackendRemote, self).__init__()
        self.bz3 = BackendZ3()
        self.local_timeout = local_timeout

    def solver(self, timeout=None):
        timeout = self.local_timeout if timeout is None else min(self.local_timeout, timeout)
        return TrackingSolver(self.bz3.solver(timeout=timeout))

    #def _abstract(self, e):
    #   return e

    def _convert(self, e):
        return e

    def resolve(self, ast):
        return ast

    def _add(self, s, c):
        s.constraints.extend(c)
        self.bz3.add(s.sz3, c)

    def _check(self, s, extra_constraints=()):
        for x in s.plus_extra(extra_constraints):
            if hasattr(x, 'make_uuid'):
                x.make_uuid()
        # print(pickle.dumps(s.plus_extra(extra_constraints)))
        res = remotetasks.check.delay(s.plus_extra(extra_constraints))
        return get(res)

    def _eval(self, expr, n, solver=None, extra_constraints=()):
        for x in solver.plus_extra(extra_constraints):
            if hasattr(x, 'make_uuid'):
                x.make_uuid()
        # print(pickle.dumps(s.plus_extra(extra_constraints)))
        res = remotetasks.eval.delay(solver.plus_extra(extra_constraints), expr, n)
        return get(res)

    def _batch_eval(self, exprs, n, extra_constraints=(), solver=None):
        for x in solver.plus_extra(extra_constraints):
            if hasattr(x, 'make_uuid'):
                x.make_uuid()
        res = remotetasks.batch_eval.delay(solver.plus_extra(extra_constraints), exprs, n)
        return get(res)

    def _results(self, s, extra_constraints=(), generic_model=True):
        for x in s.plus_extra(extra_constraints):
            if hasattr(x, 'make_uuid'):
                x.make_uuid()
        # print(pickle.dumps(s.plus_extra(extra_constraints)))
        res = remotetasks.results.delay(s.plus_extra(extra_constraints))
        return get(res)

    def _min(self, expr, solver=None, extra_constraints=()):
        for x in solver.plus_extra(extra_constraints):
            if hasattr(x, 'make_uuid'):
                x.make_uuid()
        # print(pickle.dumps(s.plus_extra(extra_constraints)))
        res = remotetasks.min.delay(solver.plus_extra(extra_constraints), expr)
        return get(res)

    def _max(self, expr, extra_constraints=(), solver=None):
        for x in solver.plus_extra(extra_constraints):
            if hasattr(x, 'make_uuid'):
                x.make_uuid()
        # print(pickle.dumps(s.plus_extra(extra_constraints)))
        res = remotetasks.max.delay(solver.plus_extra(extra_constraints), expr)
        return get(res)

    def _name(self, o):
        raise Exception('wat') # TODO: Be more explicit :p

    def _identical(self, a, b):
        return a.identical(b)
