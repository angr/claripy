import functools
import struct

from .errors import ClaripyOperationError
from .backend_object import BackendObject

def compare_sorts(f):
    @functools.wraps(f)
    def compare_guard(self, o):
        if self.sort != o.sort:
            raise TypeError("FPVs are differently-sorted ({} and {})".format(self.sort, o.sort))
        return f(self, o)

    return compare_guard

def normalize_types(f):
    @functools.wraps(f)
    def normalize_helper(self, o):
        if isinstance(o, float):
            o = FPV(o, self.sort)

        if not isinstance(self, FPV) or not isinstance(o, FPV):
            raise TypeError("must have two FPVs")

        return f(self, o)

    return normalize_helper

class RM(str):
    @staticmethod
    def default():
        return RM_RNE

    @staticmethod
    def from_name(name):
        return {
            'RM_RNE': RM_RNE,
            'RM_RNA': RM_RNA,
            'RM_RTP': RM_RTP,
            'RM_RTN': RM_RTN,
            'RM_RTZ': RM_RTZ,
        }[name]

RM_RNE = RM('RNE')
RM_RNA = RM('RNA')
RM_RTP = RM('RTP')
RM_RTN = RM('RTN')
RM_RTZ = RM('RTZ')

class FSort(object):
    def __init__(self, name, exp, mantissa):
        self.name = name
        self.exp = exp
        self.mantissa = mantissa

    def __eq__(self, other):
        return self.exp == other.exp and self.mantissa == other.mantissa

    def __repr__(self):
        return self.name

    @property
    def length(self):
        return self.exp + self.mantissa

    @staticmethod
    def from_size(n):
        if n == 32:
            return FSORT_FLOAT
        elif n == 64:
            return FSORT_DOUBLE
        else:
            raise ClaripyOperationError('{} is not a valid FSort size'.format(n))

    @staticmethod
    def from_params(exp, mantissa):
        if exp == 8 and mantissa == 24:
            return FSORT_FLOAT
        elif exp == 11 and mantissa == 53:
            return FSORT_DOUBLE
        else:
            raise ClaripyOperationError("unrecognized FSort params")

FSORT_FLOAT = FSort('FLOAT', 8, 24)
FSORT_DOUBLE = FSort('DOUBLE', 11, 53)


class FPV(BackendObject):
    __slots__ = ['sort', 'value']

    def __init__(self, value, sort):
        if not isinstance(value, float) or sort not in {FSORT_FLOAT, FSORT_DOUBLE}:
            raise ClaripyOperationError("FPV needs a sort (FSORT_FLOAT or FSORT_DOUBLE) and a float value")

        self.value = value
        self.sort = sort

    def __hash__(self):
        return hash((self.value, self.sort))

    def __getstate__(self):
        return (self.value, self.sort)

    def __setstate__(self, (value, sort)):
        self.value = value
        self.sort = sort

    def __abs__(self):
        return FPV(abs(self.value), self.sort)

    def __neg__(self):
        return FPV(-self.value, self.sort)

    @normalize_types
    @compare_sorts
    def __add__(self, o):
        return FPV(self.value + o.value, self.sort)

    @normalize_types
    @compare_sorts
    def __sub__(self, o):
        return FPV(self.value - o.value, self.sort)

    @normalize_types
    @compare_sorts
    def __mul__(self, o):
        return FPV(self.value * o.value, self.sort)

    @normalize_types
    @compare_sorts
    def __mod__(self, o):
        return FPV(self.value % o.value, self.sort)

    @normalize_types
    @compare_sorts
    def __div__(self, o):
        try:
            return FPV(self.value / o.value, self.sort)
        except ZeroDivisionError:
            if str(self.value * o.value)[0] == '-':
                return FPV(float('-inf'), self.sort)
            else:
                return FPV(float('inf'), self.sort)

    #
    # Reverse arithmetic stuff
    #

    @normalize_types
    @compare_sorts
    def __radd__(self, o):
        return FPV(o.value + self.value, self.sort)

    @normalize_types
    @compare_sorts
    def __rsub__(self, o):
        return FPV(o.value - self.value, self.sort)

    @normalize_types
    @compare_sorts
    def __rmul__(self, o):
        return FPV(o.value * self.value, self.sort)

    @normalize_types
    @compare_sorts
    def __rmod__(self, o):
        return FPV(o.value % self.value, self.sort)

    @normalize_types
    @compare_sorts
    def __rdiv__(self, o):
        try:
            return FPV(o.value / self.value, self.sort)
        except ZeroDivisionError:
            if str(o.value * self.value)[0] == '-':
                return FPV(float('-inf'), self.sort)
            else:
                return FPV(float('inf'), self.sort)

    #
    # Boolean stuff
    #

    @normalize_types
    @compare_sorts
    def __eq__(self, o):
        return self.value == o.value

    @normalize_types
    @compare_sorts
    def __ne__(self, o):
        return self.value != o.value

    @normalize_types
    @compare_sorts
    def __lt__(self, o):
        return self.value < o.value

    @normalize_types
    @compare_sorts
    def __gt__(self, o):
        return self.value > o.value

    @normalize_types
    @compare_sorts
    def __le__(self, o):
        return self.value <= o.value

    @normalize_types
    @compare_sorts
    def __ge__(self, o):
        return self.value >= o.value

    def __repr__(self):
        return 'FPV({:f}, {})'.format(self.value, self.sort)

def fpToFP(a1, a2, a3=None):
    if isinstance(a1, BVV) and isinstance(a2, FSort):
        sort = a2
        if sort == FSORT_FLOAT:
            pack, unpack = 'I', 'f'
        elif sort == FSORT_DOUBLE:
            pack, unpack = 'Q', 'd'
        else:
            raise ClaripyOperationError("unrecognized float sort")

        packed = struct.pack('<' + pack, a1.value)
        unpacked, = struct.unpack('<' + unpack, packed)

        return FPV(unpacked, sort)
    elif isinstance(a1, RM) and isinstance(a2, FPV) and isinstance(a3, FSort):
        return FPV(a2.value, a3)
    elif isinstance(a1, RM) and isinstance(a2, BVV) and isinstance(a3, FSort):
        return FPV(float(a2.signed), a3)
    else:
        raise ClaripyOperationError("unknown types passed to fpToFP")

def fpToFPUnsigned(_rm, thing, sort):
    # thing is a BVV
    return FPV(float(thing.value), sort)

def fpToIEEEBV(fpv):
    if fpv.sort == FSORT_FLOAT:
        pack, unpack = 'f', 'I'
    elif fpv.sort == FSORT_DOUBLE:
        pack, unpack = 'd', 'Q'
    else:
        raise ClaripyOperationError("unrecognized float sort")

    packed = struct.pack('<' + pack, fpv.value)
    unpacked, = struct.unpack('<' + unpack, packed)

    return BVV(unpacked, fpv.sort.length)

def fpFP(sgn, exp, mantissa):
    concatted = Concat(sgn, exp, mantissa)
    sort = FSort.from_size(concatted.size())

    if sort == FSORT_FLOAT:
        pack, unpack = 'I', 'f'
    elif sort == FSORT_DOUBLE:
        pack, unpack = 'Q', 'd'
    else:
        raise ClaripyOperationError("unrecognized float sort")

    packed = struct.pack('<' + pack, concatted.value)
    unpacked, = struct.unpack('<' + unpack, packed)

    return FPV(unpacked, sort)

def fpToSBV(rm, fp, size):
    try:
        if rm == RM_RTZ:
            return BVV(int(fp.value), size)
        elif rm == RM_RNE:
            return BVV(int(round(fp.value)), size)
        else:
            raise ClaripyOperationError("todo")
    except (ValueError, OverflowError):
        return BVV(0, size)

def fpToUBV(rm, fp, size):
    # todo: actually make unsigned
    try:
        if rm == RM_RTZ:
            return BVV(int(fp.value), size)
        elif rm == RM_RNE:
            return BVV(int(round(fp.value)), size)
        else:
            raise ClaripyOperationError("todo")
    except (ValueError, OverflowError):
        return BVV(0, size)

def fpEQ(a, b):
    return a == b

def fpGT(a, b):
    return a > b

def fpGEQ(a, b):
    return a >= b

def fpLT(a, b):
    return a < b

def fpLEQ(a, b):
    return a <= b

def fpAbs(x):
    return abs(x)

def fpNeg(x):
    return -x

def fpSub(_rm, a, b):
    return a - b

def fpAdd(_rm, a, b):
    return a + b

def fpMul(_rm, a, b):
    return a * b

def fpDiv(_rm, a, b):
    return a / b

from .bv import BVV, Concat
