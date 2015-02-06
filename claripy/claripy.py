import itertools
bitvec_counter = itertools.count()

import logging
l = logging.getLogger('claripy.claripy')

class Claripy(object):
    def __init__(self, name, model_backends, solver_backends, parallel=None):
        self.name = name
        self.solver_backends = solver_backends
        self.model_backends = model_backends
        self.unique_names = True
        self.parallel = parallel if parallel else False

        self.true = self.BoolVal(True)
        self.false = self.BoolVal(False)

    #
    # Backend management
    #
    def backend_of_type(self, b_type):
        for b in self.model_backends + self.solver_backends:
            if type(b) is b_type:
                return b
        return None

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

    def BitVec(self, name, size, explicit_name=None):
        explicit_name = explicit_name if explicit_name is not None else False
        if self.unique_names and not explicit_name:
            name = "%s_%d_%d" % (name, bitvec_counter.next(), size)
        return A(self, 'BitVec', (name, size), variables={ name }, symbolic=True, simplified=A.FULL_SIMPLIFY)
    BV = BitVec

    def BitVecVal(self, *args):
        return I(self, BVV(*args), variables=set(), symbolic=False, simplified=A.FULL_SIMPLIFY)
        #return self._do_op('BitVecVal', args, variables=set(), symbolic=False, raw=True)
    BVV = BitVecVal

    # Bitwise ops
    def LShR(self, *args): return A(self, 'LShR', args).reduced
    def SignExt(self, *args): return A(self, 'SignExt', args).reduced
    def ZeroExt(self, *args): return A(self, 'ZeroExt', args).reduced
    def Extract(self, *args): return A(self, 'Extract', args).reduced
    def Concat(self, *args):
        if len(args) == 1:
            return args[0]
        else:
            return A(self, 'Concat', args).reduced
    def RotateLeft(self, *args): return A(self, 'RotateLeft', args).reduced
    def RotateRight(self, *args): return A(self, 'RotateRight', args).reduced
    def Reverse(self, o): return A(self, 'Reverse', (o,), collapsible=False).reduced

    #
    # Strided interval
    #
    def StridedInterval(self, name=None, bits=0, lower_bound=None, upper_bound=None, stride=None, to_conv=None):
        si = BackendVSA.CreateStridedInterval(name=name,
                                            bits=bits,
                                            lower_bound=lower_bound,
                                            upper_bound=upper_bound,
                                            stride=stride,
                                            to_conv=to_conv)
        return I(self, si, variables={ si.name }, symbolic=False)
    SI = StridedInterval

    def TopStridedInterval(self, bits, name=None, signed=False):
        si = BackendVSA.CreateTopStridedInterval(bits=bits, name=name, signed=signed)
        return I(self, si, variables={ si.name }, symbolic=False)
    TSI = TopStridedInterval

    # Value Set
    def ValueSet(self, **kwargs):
        vs = ValueSet(**kwargs)
        return I(self, vs, variables={ vs.name }, symbolic=False)
    VS = ValueSet

    # a-loc
    def AbstractLocation(self, *args, **kwargs): #pylint:disable=no-self-use
        aloc = AbstractLocation(*args, **kwargs)
        return aloc

    #
    # Boolean ops
    #
    def BoolVal(self, *args):
        return I(self, args[0], variables=set(), symbolic=False)
        #return self._do_op('BoolVal', args, variables=set(), symbolic=False, raw=True)

    def And(self, *args): return A(self, 'And', args).reduced
    def Not(self, *args): return A(self, 'Not', args).reduced
    def Or(self, *args): return A(self, 'Or', args).reduced
    def ULT(self, *args): return A(self, 'ULT', args).reduced
    def ULE(self, *args): return A(self, 'ULE', args).reduced
    def UGE(self, *args): return A(self, 'UGE', args).reduced
    def UGT(self, *args): return A(self, 'UGT', args).reduced

    #
    # Other ops
    #
    def If(self, *args):
        if len(args) != 3: raise ClaripyOperationError("invalid number of args passed to If")
        return A(self, 'If', args).reduced

    #def size(self, *args): return self._do_op('size', args)

    def ite_dict(self, i, d, default):
        return self.ite_cases([ (i == c, v) for c,v in d.items() ], default)

    def ite_cases(self, cases, default):
        sofar = default
        for c,v in reversed(cases):
            sofar = self.If(c, v, sofar)
        return sofar

    def simplify(self, e):
        for b in self.model_backends:
            try: return b.simplify(e)
            except BackendError: pass

        l.debug("Simplifying via solver backend")

        for b in self.solver_backends:
            try: return b.simplify(e)
            except BackendError: pass

        l.debug("Unable to simplify expression")
        return e

    def is_true(self, e):
        for b in self.model_backends:
            try: return b.is_true(b.convert(e))
            except BackendError: pass

        l.debug("Unable to tell the truth-value of this expression")
        return False

    def is_false(self, e):
        for b in self.model_backends:
            try: return b.is_false(b.convert(e))
            except BackendError: pass

        l.debug("Unable to tell the truth-value of this expression")
        return False

    def is_identical(self, *args):
        '''
        Attempts to check if the underlying models of the expression are identical,
        even if the hashes match.

        This process is somewhat conservative: False does not necessarily mean that
        it's not identical; just that it can't (easily) be determined to be identical.
        '''
        if not all([isinstance(a, A) for a in args]):
            return False

        if len(set(hash(a) for a in args)) == 1:
            return True

        first = args[0]
        identical = None
        for o in args:
            for b in self.model_backends:
                try:
                    i = b.identical(first, o)
                    if identical is None:
                        identical = True
                    identical &= i is True
                except BackendError:
                    pass

        return identical is True

    def constraint_to_si(self, expr, side): #pylint:disable=unused-argument
        '''
        Convert a constraint to SI if possible
        :param expr:
        :return:
        '''
        si = None
        old_expr = None

        for b in self.model_backends:
            if type(b) is BackendVSA:
                old_expr, si = b.constraint_to_si(expr, side)

        if si is None:
            return None, None
        else:
            return old_expr, si

    def model_object(self, e, result=None):
        for b in self.model_backends:
            try: return b.convert(e, result=result)
            except BackendError: pass
        raise BackendError('no model backend can convert expression')

from .ast import A, I
from .backends.backend import BackendError
from .bv import BVV
from .vsa import ValueSet, AbstractLocation
from .backends import BackendVSA
from .errors import ClaripyOperationError
