import functools
import numbers

from .errors import ClaripyOperationError, ClaripyTypeError, ClaripyZeroDivisionError
from .backend_object import BackendObject
from . import debug as _d

def compare_bits(f):
    @functools.wraps(f)
    def compare_guard(self, o):
        if self.bits == 0 or o.bits == 0:
            raise ClaripyTypeError("The operation is not allowed on zero-length bitvectors.")

        if self.bits != o.bits:
            raise ClaripyTypeError("bitvectors are differently-sized (%d and %d)" % (self.bits, o.bits))
        return f(self, o)

    return compare_guard

def compare_bits_0_length(f):
    @functools.wraps(f)
    def compare_guard(self, o):
        if self.bits != o.bits:
            raise ClaripyTypeError("bitvectors are differently-sized (%d and %d)" % (self.bits, o.bits))
        return f(self, o)

    return compare_guard

def normalize_types(f):
    @functools.wraps(f)
    def normalize_helper(self, o):
        if _d._DEBUG:
            if hasattr(o, '__module__') and o.__module__ == 'z3':
                raise ValueError("this should no longer happen")
        if isinstance(o, numbers.Number):
            o = self.__class__(o, self.bits)
        if isinstance(self, numbers.Number):
            self = o.__class__(self, o.bits)

        if not isinstance(self, BVVMixin) or not isinstance(o, BVVMixin):
            return NotImplemented
        return f(self, o)

    return normalize_helper


class BVVMixin:
    __slots__ = [ 'bits', '_value', 'mod' ]

    def __init__(self, value, bits):
        if _d._DEBUG:
            if bits < 0 or not isinstance(bits, numbers.Number) or not isinstance(value, numbers.Number):
                raise ClaripyOperationError("BVV needs a non-negative length and an int value")

            if bits == 0 and value not in (0, "", None):
                raise ClaripyOperationError("Zero-length BVVs cannot have a meaningful value.")

        self.bits = bits
        self._value = 0
        self.mod = 1<<bits
        self.value = value

    def __hash__(self):
        return hash((str(self.value), self.bits))

    def __getstate__(self):
        return (self.bits, self.value)

    def __setstate__(self, s):
        self.bits = s[0]
        self.mod = 1<<self.bits
        self.value = s[1]

    @property
    def value(self):
        return self._value

    @value.setter
    def value(self, v):
        self._value = v & (self.mod - 1)

    @property
    def signed(self):
        return self._value if self._value < self.mod//2 else self._value % (self.mod//2) - (self.mod//2)

    @signed.setter
    def signed(self, v):
        self._value = v % -self.mod

    #
    # Arithmetic stuff
    #

    @normalize_types
    @compare_bits
    def __add__(self, o):
        return self.__class__(self.value + o.value, self.bits)

    @normalize_types
    @compare_bits
    def __sub__(self, o):
        return self.__class__(self.value - o.value, self.bits)

    @normalize_types
    @compare_bits
    def __mul__(self, o):
        return self.__class__(self.value * o.value, self.bits)

    @normalize_types
    @compare_bits
    def __mod__(self, o):
        if o.value == 0:
            raise ClaripyZeroDivisionError()
        return self.__class__(self.value % o.value, self.bits)

    @normalize_types
    @compare_bits
    def __floordiv__(self, o):
        if o.value == 0:
            raise ClaripyZeroDivisionError()
        return self.__class__(self.value // o.value, self.bits)

    def __truediv__(self, other):
        return self // other # decline to implicitly have anything to do with floats

    def __div__(self, other):
        return self // other

    #
    # Byte-wise operations
    #

    def concat(self, *args):
        return Concat(*args)

    @property
    def reversed(self):
        # swap endianness
        return Reverse(self)

    #
    # Reverse arithmetic stuff
    #

    @normalize_types
    @compare_bits
    def __radd__(self, o):
        return self.__class__(self.value + o.value, self.bits)

    @normalize_types
    @compare_bits
    def __rsub__(self, o):
        return self.__class__(o.value - self.value, self.bits)

    @normalize_types
    @compare_bits
    def __rmul__(self, o):
        return self.__class__(self.value * o.value, self.bits)

    @normalize_types
    @compare_bits
    def __rmod__(self, o):
        if self.value == 0:
            raise ClaripyZeroDivisionError()
        return self.__class__(o.value % self.value, self.bits)

    @normalize_types
    @compare_bits
    def __rfloordiv__(self, o):
        if self.value == 0:
            raise ClaripyZeroDivisionError()
        return self.__class__(o.value // self.value, self.bits)

    def __rdiv__(self, o):
        return self.__rfloordiv__(o)

    def __rtruediv__(self, o):
        return self.__rfloordiv__(o)

    #
    # Bit operations
    #

    @normalize_types
    @compare_bits
    def __and__(self, o):
        return self.__class__(self.value & o.value, self.bits)

    @normalize_types
    @compare_bits
    def __or__(self, o):
        return self.__class__(self.value | o.value, self.bits)

    @normalize_types
    @compare_bits
    def __xor__(self, o):
        return self.__class__(self.value ^ o.value, self.bits)

    @normalize_types
    @compare_bits
    def __lshift__(self, o):
        if o.signed < self.bits:
            return self.__class__(self.value << o.signed, self.bits)
        else:
            return self.__class__(0, self.bits)

    @normalize_types
    @compare_bits
    def __rshift__(self, o):
        # arithmetic shift uses the signed version
        if o.signed < self.bits:
            return self.__class__(self.signed >> o.signed, self.bits)
        else:
            return self.__class__(0, self.bits)

    def __invert__(self):
        return self.__class__(self.value ^ self.mod-1, self.bits)

    def __neg__(self):
        return self.__class__((-self.value) % self.mod, self.bits)

    def __getitem__(self, rng):
        if type(rng) is slice:
            left = rng.start if rng.start is not None else self.bits-1
            right = rng.stop if rng.stop is not None else 0
            if left < 0:
                left = self.bits + left
            if right < 0:
                right = self.bits + right
            return Extract(left, right, self)
        else:
            return Extract(int(rng), int(rng), self)

    def zero_extend(self, n):
        return ZeroExt(n, self)

    def sign_extend(self, n):
        return SignExt(n, self)

    #
    # Reverse bit operations
    #

    @normalize_types
    @compare_bits
    def __rand__(self, o):
        return self.__class__(self.value & o.value, self.bits)

    @normalize_types
    @compare_bits
    def __ror__(self, o):
        return self.__class__(self.value | o.value, self.bits)

    @normalize_types
    @compare_bits
    def __rxor__(self, o):
        return self.__class__(self.value ^ o.value, self.bits)

    @normalize_types
    @compare_bits
    def __rlshift__(self, o):
        return self.__class__(o.value << self.signed, self.bits)

    @normalize_types
    @compare_bits
    def __rrshift__(self, o):
        return self.__class__(o.signed >> self.signed, self.bits)

    #
    # Boolean stuff
    #

    @normalize_types
    @compare_bits_0_length
    def __eq__(self, o):
        return self.value == o.value

    @normalize_types
    @compare_bits_0_length
    def __ne__(self, o):
        return self.value != o.value

    @normalize_types
    @compare_bits
    def __lt__(self, o):
        return self.value < o.value

    @normalize_types
    @compare_bits
    def __gt__(self, o):
        return self.value > o.value

    @normalize_types
    @compare_bits
    def __le__(self, o):
        return self.value <= o.value

    @normalize_types
    @compare_bits
    def __ge__(self, o):
        return self.value >= o.value

    #
    # Conversions
    #

    def size(self):
        return self.bits

    def __repr__(self):
        return 'BVV(0x%x, %d)' % (self.value, self.bits)


class BVV(BVVMixin, BackendObject):
    pass


#
# External stuff
#

__add__ = BVVMixin.__add__
__sub__ = BVVMixin.__sub__
__eq__ = BVVMixin.__eq__
__mul__ = BVVMixin.__mul__
__div__ = BVVMixin.__div__

def BitVecVal(value, bits):
    return BVV(value, bits)

def ZeroExt(num, o):
    return o.__class__(o.value, o.bits + num)

def SignExt(num, o):
    return o.__class__(o.signed, o.bits + num)

def Extract(f, t, o):
    return o.__class__((o.value >> t) & (2**(f+1) - 1), f-t+1)

def Concat(*args):
    total_bits = 0
    total_value = 0

    for o in args:
        total_value = (total_value << o.bits) | o.value
        total_bits += o.bits
    return args[0].__class__(total_value, total_bits)

def RotateRight(self, bits):
    bits_smaller = bits % self.size()
    return LShR(self, bits_smaller) | (self << (self.size()-bits_smaller))

def RotateLeft(self, bits):
    bits_smaller = bits % self.size()
    return (self << bits_smaller) | (LShR(self, (self.size()-bits_smaller)))

def Reverse(a):
    size = a.size()
    if size == 8:
        return a
    elif size % 8 != 0:
        raise ClaripyOperationError("can't reverse non-byte sized bitvectors")
    else:
        value = a.value
        out = 0
        if size == 64:
            out = _reverse_64(value)
        elif size == 32:
            out = _reverse_32(value)
        elif size == 16:
            out = _reverse_16(value)
        else:
            for i in range(0, size, 8):
                out |= ((value & (0xff << i)) >> i) << (size - 8 - i)
        return a.__class__(out, size)

        # the RIGHT way to do it:
        #return BVV(int(("%x" % a.value).rjust(size/4, '0').decode('hex')[::-1].encode('hex'), 16), size)

def _reverse_16(v):
    return ((v & 0xff) << 8) | \
           ((v & 0xff00) >> 8)

def _reverse_32(v):
    return ((v & 0xff) << 24) | \
           ((v & 0xff00) << 8) | \
           ((v & 0xff0000) >> 8) | \
           ((v & 0xff000000) >> 24)

def _reverse_64(v):
    return ((v & 0xff) << 56) | \
           ((v & 0xff00) << 40) | \
           ((v & 0xff0000) << 24) | \
           ((v & 0xff000000) << 8) | \
           ((v & 0xff00000000) >> 8) | \
           ((v & 0xff0000000000) >> 24) | \
           ((v & 0xff000000000000) >> 40) | \
           ((v & 0xff00000000000000) >> 56)

@normalize_types
@compare_bits
def ULT(self, o):
    return self.value < o.value

@normalize_types
@compare_bits
def UGT(self, o):
    return self.value > o.value

@normalize_types
@compare_bits
def ULE(self, o):
    return self.value <= o.value

@normalize_types
@compare_bits
def UGE(self, o):
    return self.value >= o.value

@normalize_types
@compare_bits
def SLT(self, o):
    return self.signed < o.signed

__lt__ = SLT

@normalize_types
@compare_bits
def SGT(self, o):
    return self.signed > o.signed

__gt__ = SGT

@normalize_types
@compare_bits
def SLE(self, o):
    return self.signed <= o.signed

@normalize_types
@compare_bits
def SGE(self, o):
    return self.signed >= o.signed

@normalize_types
@compare_bits
def SMod(self, o):
    # compute the remainder like the % operator in C
    a = self.signed
    b = o.signed
    if b == 0:
        raise ClaripyZeroDivisionError()
    division_result = a//b if a*b>0 else (a+(-a%b))//b
    val = a - division_result*b
    return BVV(val, self.bits)

@normalize_types
@compare_bits
def SDiv(self, o):
    # compute the round towards 0 division
    a = self.signed
    b = o.signed
    if b == 0:
        raise ClaripyZeroDivisionError()
    val = a//b if a*b>0 else (a+(-a%b))//b
    return BVV(val, self.bits)

#
# Pure boolean stuff
#

def BoolV(b):
    return b

def And(*args):
    return all(args)

def Or(*args):
    return any(args)

def Not(b):
    return not b

@normalize_types
def normalizer(*args):
    return args

def If(c, t, f):
    t,f = normalizer(t,f) #pylint:disable=unbalanced-tuple-unpacking
    if c: return t
    else: return f

@normalize_types
@compare_bits
def LShR(a, b):
    return BVV(a.value >> b.signed, a.bits)
