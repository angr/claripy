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

        raise Exception("no backend can handle operation %s", name)

    def And(self, *args): return self._do_op('', args)
    def BitVecVal(self, *args): return self._do_op('', args)
    def ULT(self, *args): return self._do_op('', args)
    def SignExt(self, *args): return self._do_op('', args)
    def LShR(self, *args): return self._do_op('', args)
    def BoolVal(self, *args): return self._do_op('', args)
    def BitVec(self, *args): return self._do_op('', args)
    def ZeroExt(self, *args): return self._do_op('', args)
    def UGE(self, *args): return self._do_op('', args)
    def If(self, *args): return self._do_op('', args)
    def Not(self, *args): return self._do_op('', args)
    def ULE(self, *args): return self._do_op('', args)
    def Extract(self, *args): return self._do_op('', args)
    def Or(self, *args): return self._do_op('', args)
    def Concat(self, *args): return self._do_op('', args)
    def UGT(self, *args): return self._do_op('', args)
    def RotateLeft(self, *args): return self._do_op('', args)
    def RotateRight(self, *args): return self._do_op('', args)

from .backends import BackendError
