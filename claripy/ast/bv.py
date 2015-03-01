from ..operations import op, length_same_check, basic_length_calc
from ..bv import BVV

from .base import make_methods, I
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
    def _from_int(like, value):
        return BVI(like._claripy, BVV(value, like.length), length=like.length)

    @staticmethod
    def _from_long(like, value):
        return BVI(like._claripy, BVV(value, like.length), length=like.length)

BV.__add__ = op('Add', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__radd__ = op('RAdd', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__div__ = op('Div', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__rdiv__ = op('RDiv', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__truediv__ = op('TrueDiv', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__rtruediv__ = op('RTrueDiv', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__floordiv__ = op('FloorDiv', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__rfloordiv__ = op('RFloorDiv', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__mul__ = op('Mul', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__rmul__ = op('RMul', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__sub__ = op('Sub', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__rsub__ = op('RSub', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__pow__ = op('Pow', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__rpow__ = op('RPow', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__mod__ = op('Mod', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__rmod__ = op('RMod', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__divmod__ = op('DivMod', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)
BV.__rdivmod__ = op('RDivMod', (BV, BV), BV, extra_check=length_same_check, calc_length=basic_length_calc)

BV.__neg__ = op('Neg', (BV,), BV, calc_length=basic_length_calc)
BV.__pos__ = op('Pos', (BV,), BV, calc_length=basic_length_calc)
BV.__abs__ = op('Abs', (BV,), BV, calc_length=basic_length_calc)

BV.__eq__ = op('Eq', (BV, BV), Bool, extra_check=length_same_check)
BV.__ne__ = op('Ne', (BV, BV), Bool, extra_check=length_same_check)
BV.__ge__ = op('Ge', (BV, BV), Bool, extra_check=length_same_check)
BV.__le__ = op('Le', (BV, BV), Bool, extra_check=length_same_check)
BV.__gt__ = op('Gt', (BV, BV), Bool, extra_check=length_same_check)
BV.__lt__ = op('Lt', (BV, BV), Bool, extra_check=length_same_check)


BV.reversed = property(op('Reversed', (BV,), BV, calc_length=basic_length_calc))
#def foo(self):
#    raise Exception("foo called");
#BV.reversed = property(foo)

#make_methods(BV, expression_arithmetic_operations | expression_comparator_operations | expression_bitwise_operations)

class BVI(I, BV):
    @staticmethod
    def _check_model_type(model):
        if not isinstance(model, BVV):
            raise ClaripyTypeError("BVI model must be a BVV")

from ..bv import BVV
