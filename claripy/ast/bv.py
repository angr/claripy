from .bits import Bits
from ..ast.base import Base, _make_name

_bvv_cache = dict()

class BV(Bits):

    # TODO: do these go on Bits or BV?
    def chop(self, bits=1):
        '''
        Chops an AST into ASTs of size 'bits'. Obviously, the length of the AST must be
        a multiple of bits.
        '''
        s = len(self)
        if s % bits != 0:
            raise ValueError("expression length (%d) should be a multiple of 'bits' (%d)" % (len(self), bits))
        elif s == bits:
            return [ self ]
        else:
            return list(reversed([ self[(n+1)*bits - 1:n*bits] for n in range(0, s / bits) ]))

    def __getitem__(self, rng):
        '''
        Extracts bits from the AST. ASTs are indexed weirdly. For a 32-bit AST:

            a[31] is the *LEFT* most bit, so it'd be the 0 in

                01111111111111111111111111111111

            a[0] is the *RIGHT* most bit, so it'd be the 0 in

                11111111111111111111111111111110

            a[31:30] are the two leftmost bits, so they'd be the 0s in:

                00111111111111111111111111111111

            a[1:0] are the two rightmost bits, so they'd be the 0s in:

                11111111111111111111111111111100

        @returns the new AST.
        '''
        if type(rng) is slice:
            return Extract(int(rng.start), int(rng.stop), self)
        else:
            return Extract(int(rng), int(rng), self)

    def zero_extend(self, n):
        '''
        Zero-extends the AST by n bits. So:

            a = BVV(0b1111, 4)
            b = a.zero_extend(4)
            b is BVV(0b00001111)
        '''
        return ZeroExt(n, self)

    def sign_extend(self, n):
        '''
        Sign-extends the AST by n bits. So:

            a = BVV(0b1111, 4)
            b = a.sign_extend(4)
            b is BVV(0b11111111)
        '''
        return SignExt(n, self)

    def concat(self, *args):
        '''
        Concatenates this AST with the ASTs provided.
        '''
        return Concat(self, *args)

    @staticmethod
    def _from_int(like, value):
        return BVI(bv.BVV(value, like.length), length=like.length)

    @staticmethod
    def _from_long(like, value):
        return BVI(bv.BVV(value, like.length), length=like.length)

    @staticmethod
    def _from_BVV(like, value): #pylint:disable=unused-argument
        return BVI(value, length=value.size())

    def signed_to_fp(self, rm, sort):
        if rm is None:
            rm = fp.fp.RM.default()

        return fp.fpToFP(rm, self, sort)

    def unsigned_to_fp(self, rm, sort):
        if rm is None:
            rm = fp.fp.RM.default()
        return fp.fpToFPUnsigned(rm, self, sort)

    def raw_to_fp(self):
        sort = fp.fp.FSort.from_size(self.length)
        return fp.fpToFP(self, sort)

    def to_bv(self):
        return self

def BVI(model, **kwargs):
    eager = isinstance(model, bv.BVV)
    kwargs['eager'] = eager
    return BV('I', (model,), **kwargs)

def BitVec(name, size, explicit_name=False):
    n = _make_name(name, size, explicit_name)
    return BV('BitVec', (n, size), variables={n}, symbolic=True, simplified=Base.FULL_SIMPLIFY, length=size)

def BitVecVal(value, size, name=None, explicit_name=False, variables=frozenset()):
    if name is not None:
        n = _make_name(name, size, explicit_name=explicit_name)
        variables = variables | frozenset((n,))
    # when it has no name or variables we try to get it from the constant cache
    if len(variables) == 0:
        global _bvv_cache
        try:
            return _bvv_cache[(value, size)]
        except KeyError:
            result = BVI(bv.BVV(value, size), variables=variables, symbolic=False, simplified=Base.FULL_SIMPLIFY, length=size, eager=True)
            _bvv_cache[(value, size)] = result
            return result
    return BVI(bv.BVV(value, size), variables=variables, symbolic=False, simplified=Base.FULL_SIMPLIFY, length=size, eager=True)

def StridedInterval(name=None, bits=0, lower_bound=None, upper_bound=None, stride=None, to_conv=None):
    si = vsa.CreateStridedInterval(name=name, bits=bits, lower_bound=lower_bound, upper_bound=upper_bound, stride=stride, to_conv=to_conv)
    return BVI(si, variables={ si.name }, symbolic=False, length=si._bits, eager=False)

def TopStridedInterval(bits, name=None, uninitialized=False):
    si = vsa.StridedInterval.top(bits, name=name, uninitialized=uninitialized)
    return BVI(si, variables={ si.name }, symbolic=False, length=bits)

def EmptyStridedInterval(bits, name=None):
    si = vsa.StridedInterval.empty(bits)
    return BVI(si, variables={ si.name }, symbolic=False, length=bits)

def ValueSet(**kwargs):
    vs = vsa.ValueSet(**kwargs)
    return BVI(vs, variables={ vs.name }, symbolic=False, length=kwargs['bits'], eager=False)

#
# Unbound operations
#

from .bool import Bool
from .. import operations

# comparisons
ULT = operations.op('ULT', (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)
ULE = operations.op('ULE', (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)
UGT = operations.op('UGT', (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)
UGE = operations.op('UGE', (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)
SLT = operations.op('SLT', (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)
SLE = operations.op('SLE', (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)
SGT = operations.op('SGT', (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)
SGE = operations.op('SGE', (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)

# bit stuff
LShR = operations.op('LShR', (BV, BV), BV, extra_check=operations.length_same_check,
                     calc_length=operations.basic_length_calc, bound=False)
SignExt = operations.op('SignExt', ((int, long), BV), BV,
                        calc_length=operations.ext_length_calc, bound=False)
ZeroExt = operations.op('ZeroExt', ((int, long), BV), BV,
                        calc_length=operations.ext_length_calc, bound=False)
Extract = operations.op('Extract', ((int, long), (int, long), BV),
                        BV, extra_check=operations.extract_check,
                        calc_length=operations.extract_length_calc, bound=False)

Concat = operations.op('Concat', BV, BV, calc_length=operations.concat_length_calc, bound=False)

RotateLeft = operations.op('RotateLeft', (BV, BV), BV,
                           extra_check=operations.length_same_check,
                           calc_length=operations.basic_length_calc, bound=False)
RotateRight = operations.op('RotateRight', (BV, BV), BV,
                            extra_check=operations.length_same_check,
                            calc_length=operations.basic_length_calc, bound=False)
Reverse = operations.op('Reverse', (BV,), BV,
                        calc_length=operations.basic_length_calc, bound=False)

#
# Bound operations
#

BV.__add__ = operations.op('__add__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__radd__ = operations.op('__radd__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__div__ = operations.op('__div__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rdiv__ = operations.op('__rdiv__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__truediv__ = operations.op('__truediv__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rtruediv__ = operations.op('__rtruediv__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__floordiv__ = operations.op('__floordiv__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rfloordiv__ = operations.op('__rfloordiv__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__mul__ = operations.op('__mul__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rmul__ = operations.op('__rmul__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__sub__ = operations.op('__sub__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rsub__ = operations.op('__rsub__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__pow__ = operations.op('__pow__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rpow__ = operations.op('__rpow__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__mod__ = operations.op('__mod__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rmod__ = operations.op('__rmod__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__divmod__ = operations.op('__divmod__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rdivmod__ = operations.op('__rdivmod__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)

BV.__neg__ = operations.op('__neg__', (BV,), BV, calc_length=operations.basic_length_calc)
BV.__pos__ = operations.op('__pos__', (BV,), BV, calc_length=operations.basic_length_calc)
BV.__abs__ = operations.op('__abs__', (BV,), BV, calc_length=operations.basic_length_calc)

BV.__eq__ = operations.op('__eq__', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.__ne__ = operations.op('__ne__', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.__ge__ = operations.op('__ge__', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.__le__ = operations.op('__le__', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.__gt__ = operations.op('__gt__', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.__lt__ = operations.op('__lt__', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.SLT = operations.op('SLT', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.SGT = operations.op('SGT', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.SLE = operations.op('SLE', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.SGE = operations.op('SGE', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.ULT = operations.op('ULT', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.UGT = operations.op('UGT', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.ULE = operations.op('ULE', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.UGE = operations.op('UGE', (BV, BV), Bool, extra_check=operations.length_same_check)

BV.__invert__ = operations.op('__invert__', (BV,), BV, calc_length=operations.basic_length_calc)
BV.__or__ = operations.op('__or__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__ror__ = operations.op('__ror__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__and__ = operations.op('__and__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rand__ = operations.op('__rand__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__xor__ = operations.op('__xor__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rxor__ = operations.op('__rxor__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__lshift__ = operations.op('__lshift__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rlshift__ = operations.op('__rlshift__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rshift__ = operations.op('__rshift__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rrshift__ = operations.op('__rrshift__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.LShR = operations.op('LShR', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)

BV.Extract = staticmethod(operations.op('Extract', ((int, long), (int, long), BV), BV, extra_check=operations.extract_check, calc_length=operations.extract_length_calc, bound=False))
BV.Concat = staticmethod(operations.op('Concat', BV, BV, calc_length=operations.concat_length_calc, bound=False))
BV.reversed = property(operations.op('Reverse', (BV,), BV, calc_length=operations.basic_length_calc))

BV.union = operations.op('union', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.widen = operations.op('widen', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.intersection = operations.op('intersection', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)

from .. import bv
from .. import fp
from . import fp
from .. import vsa
