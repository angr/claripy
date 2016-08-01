import functools
from .errors import ClaripyOperationError, ClaripyTypeError, ClaripyZeroDivisionError
from .backend_object import BackendObject

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
        if hasattr(o, '__module__') and o.__module__ == 'z3':
            raise ValueError("this should no longer happen")
        if type(o) in (int, long):
            o = BVV(o, self.bits)
        if type(self) in (int, long):
            self = BVV(self, self.bits)

        if not isinstance(self, BVV) or not isinstance(o, BVV):
            return NotImplemented
        return f(self, o)

    return normalize_helper

class BVV(BackendObject):
    __slots__ = [ 'bits', '_value', 'mod', 'value' ]

    def __init__(self, value, bits):
        if bits < 0 or type(bits) not in (int, long) or type(value) not in (int, long):
            raise ClaripyOperationError("BVV needs a non-negative length and an int/long value")

        if bits == 0 and value not in (0, "", None):
            raise ClaripyOperationError("Zero-length BVVs cannot have a meaningful value.")

        self.bits = bits
        self._value = 0
        self.mod = 2**bits
        self.value = value

    def __hash__(self):
        return hash((str(self.value), self.bits))

    def __getstate__(self):
        return (self.bits, self.value)

    def __setstate__(self, s):
        self.bits = s[0]
        self.mod = 2**self.bits
        self.value = s[1]

    @property
    def value(self):
        return self._value

    @value.setter
    def value(self, v):
        self._value = v & (self.mod - 1)

    @property
    def signed(self):
        return self._value if self._value < self.mod/2 else self._value % (self.mod/2) - (self.mod/2)

    @signed.setter
    def signed(self, v):
        self._value = v % -self.mod

    #
    # Arithmetic stuff
    #

    @normalize_types
    @compare_bits
    def __add__(self, o):
        return BVV(self.value + o.value, self.bits)

    @normalize_types
    @compare_bits
    def __sub__(self, o):
        return BVV(self.value - o.value, self.bits)

    @normalize_types
    @compare_bits
    def __mul__(self, o):
        return BVV(self.value * o.value, self.bits)

    @normalize_types
    @compare_bits
    def __mod__(self, o):
        try:
            return BVV(self.value % o.value, self.bits)
        except ZeroDivisionError:
            raise ClaripyZeroDivisionError()

    @normalize_types
    @compare_bits
    def __div__(self, o):
        try:
            return BVV(self.value / o.value, self.bits)
        except ZeroDivisionError:
            raise ClaripyZeroDivisionError()

    #
    # Reverse arithmetic stuff
    #

    @normalize_types
    @compare_bits
    def __radd__(self, o):
        return BVV(self.value + o.value, self.bits)

    @normalize_types
    @compare_bits
    def __rsub__(self, o):
        return BVV(o.value - self.value, self.bits)

    @normalize_types
    @compare_bits
    def __rmul__(self, o):
        return BVV(self.value * o.value, self.bits)

    @normalize_types
    @compare_bits
    def __rmod__(self, o):
        return BVV(o.value % self.value, self.bits)

    @normalize_types
    @compare_bits
    def __rdiv__(self, o):
        return BVV(o.value / self.value, self.bits)

    #
    # Bit operations
    #

    @normalize_types
    @compare_bits
    def __and__(self, o):
        return BVV(self.value & o.value, self.bits)

    @normalize_types
    @compare_bits
    def __or__(self, o):
        return BVV(self.value | o.value, self.bits)

    @normalize_types
    @compare_bits
    def __xor__(self, o):
        return BVV(self.value ^ o.value, self.bits)

    @normalize_types
    @compare_bits
    def __lshift__(self, o):
        if o.signed < self.bits:
            return BVV(self.value << o.signed, self.bits)
        else:
            return BVV(0, self.bits)

    @normalize_types
    @compare_bits
    def __rshift__(self, o):
        # arithmetic shift uses the signed version
        if o.signed < self.bits:
            return BVV(self.signed >> o.signed, self.bits)
        else:
            return BVV(0, self.bits)

    def __invert__(self):
        return BVV(self.value ^ self.mod-1, self.bits)

    def __neg__(self):
        return BVV((-self.value) % self.mod, self.bits)

    #
    # Reverse bit operations
    #

    @normalize_types
    @compare_bits
    def __rand__(self, o):
        return BVV(self.value & o.value, self.bits)

    @normalize_types
    @compare_bits
    def __ror__(self, o):
        return BVV(self.value | o.value, self.bits)

    @normalize_types
    @compare_bits
    def __rxor__(self, o):
        return BVV(self.value ^ o.value, self.bits)

    @normalize_types
    @compare_bits
    def __rlshift__(self, o):
        return BVV(o.value << self.signed, self.bits)

    @normalize_types
    @compare_bits
    def __rrshift__(self, o):
        return BVV(o.signed >> self.signed, self.bits)

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

#
# External stuff
#

def BitVecVal(value, bits):
    return BVV(value, bits)

def ZeroExt(num, o):
    return BVV(o.value, o.bits + num)

def SignExt(num, o):
    return BVV(o.signed, o.bits + num)

def Extract(f, t, o):
    return BVV((o.value >> t) & (2**(f+1) - 1), f-t+1)

def Concat(*args):
    total_bits = 0
    total_value = 0

    for o in args:
        total_value = (total_value << o.bits) | o.value
        total_bits += o.bits
    return BVV(total_value, total_bits)

def RotateRight(self, bits):
    return LShR(self, bits) | (self << (self.size()-bits))

def RotateLeft(self, bits):
    return (self << bits) | (LShR(self, (self.size()-bits)))

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
            for i in xrange(0, size, 8):
                out |= ((value & (0xff << i)) >> i) << (size - 8 - i)
        return BVV(out, size)

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

@normalize_types
@compare_bits
def SGT(self, o):
    return self.signed > o.signed

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
    division_result = a//b if a*b>0 else (a+(-a%b))//b
    val = a - division_result*b
    return BVV(val, self.bits)

@normalize_types
@compare_bits
def SDiv(self, o):
    # compute the round towards 0 division
    a = self.signed
    b = o.signed
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
