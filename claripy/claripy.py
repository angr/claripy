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
        return BV(self, 'BitVec', (name, size), variables={ name }, symbolic=True, simplified=Base.FULL_SIMPLIFY, length=size)
    BV = BitVec

    def BitVecVal(self, value, size):
        return BVI(self, BVV(value, size), variables=set(), symbolic=False, simplified=Base.FULL_SIMPLIFY, length=size, eager=True)
    BVV = BitVecVal

    def FP(self, name, sort, explicit_name=None):
        if self.unique_names and not explicit_name:
            name = "FP_%s_%d_%d" % (name, fp_counter.next(), size)
        return FP(self, 'FP', (name, sort), variables={name}, symbolic=True, simplified=Base.FULL_SIMPLIFY)

    def FPV(self, *args):
        return FPI(self, FPV(*args), variables=set(), symbolic=False, simplified=Base.FULL_SIMPLIFY, eager=True)

    # Bitwise ops
    # def LShR(self, *args): return BV(self, 'LShR', args).reduced
    # def SignExt(self, *args): return BV(self, 'SignExt', args).reduced
    # def ZeroExt(self, *args): return BV(self, 'ZeroExt', args).reduced
    # def Extract(self, *args): return BV(self, 'Extract', args).reduced
    # def Concat(self, *args):
    #     if len(args) == 1:
    #         return args[0]
    #     else:
    #         return type(args[0])(self, 'Concat', args).reduced
    # def RotateLeft(self, *args): return BV(self, 'RotateLeft', args).reduced
    # def RotateRight(self, *args): return BV(self, 'RotateRight', args).reduced
    # def Reverse(self, o): return BV(self, 'Reverse', (o,), collapsible=False).reduced

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
        return BVI(self, si, variables={ si.name }, symbolic=False, length=bits)
    SI = StridedInterval

    def TopStridedInterval(self, bits, name=None, signed=False, uninitialized=False):
        si = BackendVSA.CreateTopStridedInterval(bits=bits, name=name, signed=signed, uninitialized=uninitialized)
        return BVI(self, si, variables={ si.name }, symbolic=False, length=bits)
    TSI = TopStridedInterval

    # Value Set
    def ValueSet(self, **kwargs):
        vs = ValueSet(**kwargs)
        return BVI(self, vs, variables={ vs.name }, symbolic=False, length=kwargs['bits'])
    VS = ValueSet

    # a-loc
    def AbstractLocation(self, *args, **kwargs): #pylint:disable=no-self-use
        aloc = AbstractLocation(*args, **kwargs)
        return aloc

    #
    # Boolean ops
    #
    def BoolVal(self, val):
        return BoolI(self, val, variables=set(), symbolic=False, eager=True)
        #return self._do_op('BoolVal', args, variables=set(), symbolic=False, raw=True)

    # def And(self, *args): return type(args[0])(self, 'And', args).reduced
    # def Not(self, *args): return type(args[0])(self, 'Not', args).reduced
    # def Or(self, *args): return type(args[0])(self, 'Or', args).reduced
    # def ULT(self, *args): return type(args[0])(self, 'ULT', args).reduced
    # def ULE(self, *args): return type(args[0])(self, 'ULE', args).reduced
    # def UGE(self, *args): return type(args[0])(self, 'UGE', args).reduced
    # def UGT(self, *args): return type(args[0])(self, 'UGT', args).reduced

    #
    # Other ops
    #
    def If(self, *args):
        # the coercion here is strange enough that we'll just implement it manually
        if len(args) != 3:
            raise ClaripyOperationError("invalid number of args passed to If")

        args = list(args)

        ty = None
        if isinstance(args[1], Base):
            ty = type(args[1])
        elif isinstance(args[2], Base):
            ty = type(args[2])
        else:
            raise ClaripyTypeError("true/false clause of If must have bearable types")

        if not isinstance(args[1], ty):
            if hasattr(ty, '_from_' + type(args[1]).__name__):
                convert = getattr(ty, '_from_' + type(args[1]).__name__)
                args[1] = convert(self, args[2], args[1])
            else:
                raise ClaripyTypeError("can't convert {} to {}".format(type(args[1]), ty))
        if not isinstance(args[2], ty):
            if hasattr(ty, '_from_' + type(args[2]).__name__):
                convert = getattr(ty, '_from_' + type(args[2]).__name__)
                args[2] = convert(self, args[1], args[2])
            else:
                raise ClaripyTypeError("can't convert {} to {}".format(type(args[2]), ty))

        if issubclass(ty, Bits):
            return ty(self, 'If', tuple(args), length=args[1].length)
        else:
            return ty(self, 'If', tuple(args)).reduced

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
        if not all([isinstance(a, Base) for a in args]):
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

    def constraint_to_si(self, expr): #pylint:disable=unused-argument
        '''
        Convert a constraint to SI if possible
        :param expr:
        :return:
        '''
        ret = True, [ ]

        for b in self.model_backends:
            if type(b) is BackendVSA:
                ret = b.constraint_to_si(expr)

        return ret

    def model_object(self, e, result=None):
        for b in self.model_backends:
            try: return b.convert(e, result=result)
            except BackendError: pass
        raise BackendError('no model backend can convert expression')

from .ast import Base, BV, BVI, FP, FPI, Bool, BoolI, Bits
from .backend import BackendError
from .bv import BVV
from .fp import FPV
from .vsa import ValueSet, AbstractLocation
from .backends import BackendVSA
from .errors import ClaripyOperationError, ClaripyTypeError
from .operations import op, length_same_check, basic_length_calc, extract_check, extract_length_calc, \
    ext_length_calc, concat_length_calc

Claripy.LShR = op('LShR', (BV, BV), BV, extra_check=length_same_check,
                  calc_length=basic_length_calc, self_is_clrp=True)
Claripy.SignExt = op('SignExt', ((int, long), BV), BV, calc_length=ext_length_calc, self_is_clrp=True)
Claripy.ZeroExt = op('ZeroExt', ((int, long), BV), BV, calc_length=ext_length_calc, self_is_clrp=True)
Claripy.Extract = op('Extract', ((int, long), (int, long), BV), BV,
                     extra_check=extract_check, calc_length=extract_length_calc, self_is_clrp=True)
Claripy.Concat = op('Concat', BV, BV, calc_length=concat_length_calc, self_is_clrp=True)
Claripy.RotateLeft = op('RotateLeft', (BV, BV), BV, extra_check=length_same_check,
                        calc_length=basic_length_calc, self_is_clrp=True)
Claripy.RotateRight = op('RotateLeft', (BV, BV), BV, extra_check=length_same_check,
                        calc_length=basic_length_calc, self_is_clrp=True)
Claripy.Reverse = op('Reverse', (BV,), BV, calc_length=basic_length_calc, self_is_clrp=True)

Claripy.And = op('And', Bool, Bool, self_is_clrp=True)
Claripy.Or = op('Or', Bool, Bool, self_is_clrp=True)
Claripy.Not = op('Not', (Bool,), Bool, self_is_clrp=True)
Claripy.ULT = op('ULT', (BV, BV), Bool, extra_check=length_same_check, self_is_clrp=True)
Claripy.ULE = op('ULE', (BV, BV), Bool, extra_check=length_same_check, self_is_clrp=True)
Claripy.UGT = op('UGT', (BV, BV), Bool, extra_check=length_same_check, self_is_clrp=True)
Claripy.UGE = op('UGE', (BV, BV), Bool, extra_check=length_same_check, self_is_clrp=True)
