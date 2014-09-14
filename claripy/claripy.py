import operator
import itertools
bitvec_counter = itertools.count()

import logging
l = logging.getLogger('claripy.claripy')

class Claripy(object):
    def __init__(self, model_backend, solver_backends, datalayer, parallel=None):
        self.solver_backends = solver_backends
        self.model_backend = model_backend
        self.datalayer = datalayer
        self.unique_names = True
        self.parallel = parallel if parallel else False

        self.true = self.BoolVal(True)
        self.false = self.BoolVal(False)

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

    def wrap(self, o):
        if type(o) == BVV:
            return self.datalayer.make_expression(o, length=o.bits)
        else:
            return o

    def _do_op(self, name, args, variables=None, symbolic=None, length=None, raw=False, simplified=False):
        try:
            if raw:
                r = self.model_backend.call(name, args)
            else:
                r = self.model_backend.call_expr(name, args)
        except BackendError:
            r = A(name, args)

        if symbolic is None:
            symbolic = any(arg.symbolic if isinstance(arg, E) else False for arg in args)
        if variables is None:
            all_variables = ((arg.variables if isinstance(arg, E) else set()) for arg in args)
            variables = reduce(operator.or_, all_variables, set())
        if length is None:
            length = op_length(name, args)

        return self.datalayer.make_expression(r, variables=variables, symbolic=symbolic, length=length, simplified=simplified)

    def BitVec(self, name, size, explicit_name=None):
        explicit_name = explicit_name if explicit_name is not None else False
        if self.unique_names and not explicit_name:
            name = "%s_%d_%d" % (name, bitvec_counter.next(), size)
        return self._do_op('BitVec', (name, size), variables={ name }, symbolic=True, length=size, raw=True, simplified=True)

    def BitVecVal(self, *args):
        return self.datalayer.make_expression(BVV(*args), variables=set(), symbolic=False, length=args[-1], simplified=True)
        #return self._do_op('BitVecVal', args, length=args[-1], variables=set(), symbolic=False, raw=True)

    # Bitwise ops
    def LShR(self, *args): return self._do_op('LShR', args)
    def SignExt(self, *args): return self._do_op('SignExt', args, length=args[0]+args[1].length)
    def ZeroExt(self, *args): return self._do_op('ZeroExt', args, length=args[0]+args[1].length)
    def Extract(self, *args): return self._do_op('Extract', args, length=args[0]-args[1]+1)
    def Concat(self, *args): return self._do_op('Concat', args, length=sum([ arg.length for arg in args ]))
    def RotateLeft(self, *args): return self._do_op('RotateLeft', args)
    def RotateRight(self, *args): return self._do_op('RotateRight', args)

    #
    # Boolean ops
    #
    def BoolVal(self, *args):
        return self.datalayer.make_expression(args[0], variables=set(), symbolic=False, length=-1, simplified=True)
        #return self._do_op('BoolVal', args, length=-1, variables=set(), symbolic=False, raw=True)

    def And(self, *args): return self._do_op('And', args, length=-1)
    def Not(self, *args): return self._do_op('Not', args, length=-1)
    def Or(self, *args): return self._do_op('Or', args, length=-1)
    def ULT(self, *args): return self._do_op('ULT', args, length=-1)
    def ULE(self, *args): return self._do_op('ULE', args, length=-1)
    def UGE(self, *args): return self._do_op('UGE', args, length=-1)
    def UGT(self, *args): return self._do_op('UGT', args, length=-1)

    #
    # Other ops
    #
    def If(self, *args):
        if len(args) != 3: raise ClaripyOperationError("invalid number of args passed to If")
        return self._do_op('If', args)

    #def size(self, *args): return self._do_op('size', args)

    def ite_dict(self, i, d, default):
        return self.ite_cases([ (i == c, v) for c,v in d.items() ], default)

    def ite_cases(self, cases, default):
        sofar = default
        for c,v in reversed(cases):
            sofar = self.If(c, v, sofar)
        return sofar

    def simplify(self, e):
        try:
            return self.model_backend.simplify_expr(e)
        except BackendError:
            try:
                for b in self.solver_backends:
                    return b.simplify_expr(e)
            except BackendError:
                pass

        l.warning("Unable to simplify expression")
        return e

from .expression import E, A
from .backends.backend import BackendError
from .operations import op_length
from .bv import BVV
from .errors import ClaripyOperationError
