from ..operations import op, length_same_check, basic_length_calc, extract_check, extract_length_calc, ext_length_calc, concat_length_calc
from ..bv import BVV

from .bits import Bits
from .bool import Bool

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
            return self._claripy.Extract(int(rng.start), int(rng.stop), self)
        else:
            return self._claripy.Extract(int(rng), int(rng), self)

    def zero_extend(self, n):
        '''
        Zero-extends the AST by n bits. So:

            a = BVV(0b1111, 4)
            b = a.zero_extend(4)
            b is BVV(0b00001111)
        '''
        return self._claripy.ZeroExt(n, self)

    def sign_extend(self, n):
        '''
        Sign-extends the AST by n bits. So:

            a = BVV(0b1111, 4)
            b = a.sign_extend(4)
            b is BVV(0b11111111)
        '''
        return self._claripy.SignExt(n, self)

    def concat(self, *args):
        '''
        Concatenates this AST with the ASTs provided.
        '''
        return self._claripy.Concat(self, *args)

    @staticmethod
    def _from_int(clrp, like, value):
        return BVI(clrp, BVV(value, like.length), length=like.length)

    @staticmethod
    def _from_long(clrp, like, value):
        return BVI(clrp, BVV(value, like.length), length=like.length)

    @staticmethod
    def _from_BVV(clrp, like, value):
        return BVI(clrp, value, length=value.size())

    def signed_to_fp(self, rm, sort):
        if rm is None:
            rm = RM.default()

        return self._claripy.fpToFP(rm, self, sort)

    def unsigned_to_fp(self, rm, sort):
        if rm is None:
            rm = RM.default()

        return self._claripy.fpToFPUnsigned(rm, self, sort)

    def raw_to_fp(self):
        sort = FSort.from_size(self.length)

        return self._claripy.fpToFP(self, sort)

    def to_bv(self):
        return self

BV.__add__ = op('__add__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__radd__ = op('__radd__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__div__ = op('__div__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__rdiv__ = op('__rdiv__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__truediv__ = op('__truediv__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__rtruediv__ = op('__rtruediv__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__floordiv__ = op('__floordiv__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__rfloordiv__ = op('__rfloordiv__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__mul__ = op('__mul__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__rmul__ = op('__rmul__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__sub__ = op('__sub__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__rsub__ = op('__rsub__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__pow__ = op('__pow__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__rpow__ = op('__rpow__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__mod__ = op('__mod__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__rmod__ = op('__rmod__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__divmod__ = op('__divmod__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__rdivmod__ = op('__rdivmod__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)

BV.__neg__ = op('__neg__', (BV,), BV, calc_length=basic_length_calc)
BV.__pos__ = op('__pos__', (BV,), BV, calc_length=basic_length_calc)
BV.__abs__ = op('__abs__', (BV,), BV, calc_length=basic_length_calc)

BV.__eq__ = op('__eq__', (BV, BV), Bool, extra_check=length_same_check)
BV.__ne__ = op('__ne__', (BV, BV), Bool, extra_check=length_same_check)
BV.__ge__ = op('__ge__', (BV, BV), Bool, extra_check=length_same_check)
BV.__le__ = op('__le__', (BV, BV), Bool, extra_check=length_same_check)
BV.__gt__ = op('__gt__', (BV, BV), Bool, extra_check=length_same_check)
BV.__lt__ = op('__lt__', (BV, BV), Bool, extra_check=length_same_check)

BV.__invert__ = op('__invert__', (BV,), BV, calc_length=basic_length_calc)
BV.__or__ = op('__or__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__ror__ = op('__ror__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__and__ = op('__and__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__rand__ = op('__rand__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__xor__ = op('__xor__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__rxor__ = op('__rxor__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__lshift__ = op('__lshift__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__rlshift__ = op('__rlshift__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__rshift__ = op('__rshift__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__rrshift__ = op('__rrshift__', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.LShR = op('LShR', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)

BV.Extract = staticmethod(op('Extract', ((int, long), (int, long), BV), BV,
                             extra_check=extract_check, calc_length=extract_length_calc,
                         self_is_clrp=True))
BV.Concat = staticmethod(op('Concat', BV, BV, calc_length=concat_length_calc, self_is_clrp=True))

BV.reversed = property(op('Reverse', (BV,), BV, calc_length=basic_length_calc))

BV.union = op('union', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.widen = op('widen', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.intersection = op('intersection', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)

def BVI(claripy, model, **kwargs):
    eager = isinstance(model, BVV)
    kwargs['eager'] = eager
    return BV(claripy, 'I', (model,), **kwargs)

from ..bv import BVV
from ..fp import RM_RTZ, FSort
