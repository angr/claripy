import itertools
bitvec_counter = itertools.count()

class Claripy(object):
    def __init__(self, expression_backends, solver_backend, results_backend):
        self.expression_backends = expression_backends
        self.solver_backend = solver_backend
        self.results_backend = results_backend

    #
    # Solvers
    #
    def solver(self):
        '''
        Returns a new solver.
        '''
        raise NotImplementedError()

    #
    # Operations
    #
    def _do_op(self, name, args):
        for b in self.expression_backends:
            try:
                return b.call(name, args)
            except BackendError:
                continue

        raise Exception("no backend can handle operation %s" % name)

    def BitVec(self, name, size):
        name = "%s_%d_%d" % (name, bitvec_counter.next(), size)
        return self._do_op('BitVec', (name, size))

    def And(self, *args): return self._do_op('And', args)
    def BitVecVal(self, *args): return self._do_op('BitVecVal', args)
    def ULT(self, *args): return self._do_op('ULT', args)
    def SignExt(self, *args): return self._do_op('SignExt', args)
    def LShR(self, *args): return self._do_op('LShR', args)
    def BoolVal(self, *args): return self._do_op('BoolVal', args)
    def ZeroExt(self, *args): return self._do_op('ZeroExt', args)
    def UGE(self, *args): return self._do_op('UGE', args)
    def If(self, *args): return self._do_op('If', args)
    def Not(self, *args): return self._do_op('Not', args)
    def ULE(self, *args): return self._do_op('ULE', args)
    def Extract(self, *args): return self._do_op('Extract', args)
    def Or(self, *args): return self._do_op('Or', args)
    def Concat(self, *args): return self._do_op('Concat', args)
    def UGT(self, *args): return self._do_op('UGT', args)
    def RotateLeft(self, *args): return self._do_op('RotateLeft', args)
    def RotateRight(self, *args): return self._do_op('RotateRight', args)

    def ite_dict(self, i, d, default):
        return self.ite_cases([ (i == c, v) for c,v in d.items() ], default)

    def ite_cases(self, cases, default):
        sofar = default
        for c,v in reversed(cases):
            sofar = self.If(c, v, sofar)
        return sofar

from .backends import BackendError
