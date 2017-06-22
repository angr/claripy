import functools
import struct

from .errors import ClaripyOperationError
from .backend_object import BackendObject

def compare_sorts(f):
    """
    Decorator, wraps backend FPV function `f(self, o)` to check if the sorts of
    the arguments match.

    :raises: TypeError
    """
    @functools.wraps(f)
    def compare_guard(self, o):
        if self.sort != o.sort:
            raise TypeError("FPVs are differently-sorted ({} and {})".format(self.sort, o.sort))
        return f(self, o)

    return compare_guard

def normalize_types(f):
    """
    Decorator, wraps backend FPV function `f(self, o)` to normalize the sort of
    `o` to a backend FPV.

    :raises: TypeError
    """
    @functools.wraps(f)
    def normalize_helper(self, o):
        if isinstance(o, float):
            o = FPV(o, self.sort)

        if not isinstance(self, FPV) or not isinstance(o, FPV):
            raise TypeError("must have two FPVs")

        return f(self, o)

    return normalize_helper

class RM(str):
    """
    Class representing the possible (IEEE 754) rounding modes.

    :param string: Name of rounding mode, must be one of 'RNE' (round to nearest,
                   ties to even), 'RNA' (round to nearest, ties away from zero),
                   'RTP' (round to positive infinity), 'RTN' (round to negative
                   infinity), 'RTZ' (round to zero).
    """
    @staticmethod
    def default():
        """
        Returns the default rounding method (round to nearest, ties to even).
        """
        return RM_RNE

    @staticmethod
    def from_name(name):
        """
        Returns the rounding mode object corresponding to the argument.

        :param name: Name of rounding mode. Must be one of 'RM_RNE', 'RM_RNA',
                     'RM_RTP', 'RM_RTN' or 'RM_RTZ'.:w

        :returns: Rounding mode object corresponding to the argument given.
        """
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
    """
    Object representing possible backend FPV sorts.

    :param self: Name of sort.
    :param exp: Size of exponent of floating point.
    :param mantissa: Size of mantissa of floating point.
    """
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
        """
        Total number of bits to represent the FPV (exponent + mantissa bits).
        """
        return self.exp + self.mantissa

    @staticmethod
    def from_size(n):
        """
        Get a floating point sort object corresponding to the given size.

        :param n: Size of floating point.

        :returns: Object representing floating point sort, currently either
                  FSORT_FLOAT (32-bits) or FSORT_DOUBLE (64 bits)
        """
        if n == 32:
            return FSORT_FLOAT
        elif n == 64:
            return FSORT_DOUBLE
        else:
            raise ClaripyOperationError('{} is not a valid FSort size'.format(n))

    @staticmethod
    def from_params(exp, mantissa):
        """
        Get a floating point sort object corresponding to the parameters.

        :param exp: Size of exponent.
        :param mantissa: Size of mantissa.

        :returns: Object representing floating point sort, currently either
                  FSORT_FLOAT (8 exponent, 24 mantissa) or FSORT_DOUBLE
                  (11 exponent, 53 mantissa)
        """
        if exp == 8 and mantissa == 24:
            return FSORT_FLOAT
        elif exp == 11 and mantissa == 53:
            return FSORT_DOUBLE
        else:
            raise ClaripyOperationError("unrecognized FSort params")

FSORT_FLOAT = FSort('FLOAT', 8, 24)
FSORT_DOUBLE = FSort('DOUBLE', 11, 53)


class FPV(BackendObject):
    """
    Object representing a concrete floating point value in the backend.

    :param value: Value of floating point.
    :param sort: FSort object representing sort of floating point.
    """
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
    """
    Convert a backend BVV into a backend FPV, or change the sort of a backend
    FPV.

    :param a1: Either a backend BVV storing a floating point value in IEEE
               format, or a rounding mode object.
    :param a2: Either a FSort object, a backend FPV or a backend BVV.
    :param a3: Either None (by default), or an FSort object.

    :returns: If `a1` is a BVV, `a2` must be an FSort object. Treat a1 as an
              IEEE float/double accordingly and returns FPV with the
              corresponding value and type.
              If `a1` is a rounding mode object, `a2` must be a FPV or BVV. In
              the former case, we return a new FPV with the same value but a
              different type. In the latter case, take the signed value of `a2`
              and return a float with that value and the specified type.
    :raises: ClaripyOperationError
    """
    if isinstance(a1, BVV) and isinstance(a2, FSort):
        sort = a2
        if sort == FSORT_FLOAT:
            pack, unpack = 'I', 'f'
        elif sort == FSORT_DOUBLE:
            pack, unpack = 'Q', 'd'
        else:
            raise ClaripyOperationError("unrecognized float sort")

        try:
            packed = struct.pack('<' + pack, a1.value)
            unpacked, = struct.unpack('<' + unpack, packed)
        except OverflowError as e:
            # struct.pack sometimes overflows
            raise ClaripyOperationError("OverflowError: " + str(e))

        return FPV(unpacked, sort)
    elif isinstance(a1, RM) and isinstance(a2, FPV) and isinstance(a3, FSort):
        return FPV(a2.value, a3)
    elif isinstance(a1, RM) and isinstance(a2, BVV) and isinstance(a3, FSort):
        return FPV(float(a2.signed), a3)
    else:
        raise ClaripyOperationError("unknown types passed to fpToFP")

def fpToFPUnsigned(_rm, thing, sort):
    """
    Convert a backend BVV representing an unsigned integer to a backend FPV of
    the same value and specified sort.

    :param _rm: Rounding mode object.
    :param thing: BVV representing an unsigned integer.
    :param sort: Sort of the FPV value to be returned.

    :returns: Extracts the unsigned value of the BVV and returns a FPV with the
              corresponding sort and value.
    """
    # thing is a BVV
    return FPV(float(thing.value), sort)

def fpToIEEEBV(fpv):
    """
    Convert a backend FPV to a backend BVV representing the float value in IEEE
    encoding.

    :param fpv: Backend FPV to convert.

    :returns: Backend BVV containing the IEEE encoding of the FPV.
    :raises: ClaripyOperationError
    """
    if fpv.sort == FSORT_FLOAT:
        pack, unpack = 'f', 'I'
    elif fpv.sort == FSORT_DOUBLE:
        pack, unpack = 'd', 'Q'
    else:
        raise ClaripyOperationError("unrecognized float sort")

    try:
        packed = struct.pack('<' + pack, fpv.value)
        unpacked, = struct.unpack('<' + unpack, packed)
    except OverflowError as e:
        # struct.pack sometimes overflows
        raise ClaripyOperationError("OverflowError: " + str(e))

    return BVV(unpacked, fpv.sort.length)

def fpFP(sgn, exp, mantissa):
    """
    Create a backend FPV from backend BVVs indicating the sign, mantissa and
    exponent of the floating point value.

    :param sgn: BVV representing the sign.
    :param exp: BVV representing the exponent.
    :param mantissa: BVV representing the mantissa.

    :returns: Concatenates the three arguments into a single BVV, and interprets
              that BVV as a float in IEEE encoding. Returns a FPV with the
              appropriate value and size.
    :raises: ClaripyOperationError
    """
    concatted = Concat(sgn, exp, mantissa)
    sort = FSort.from_size(concatted.size())

    if sort == FSORT_FLOAT:
        pack, unpack = 'I', 'f'
    elif sort == FSORT_DOUBLE:
        pack, unpack = 'Q', 'd'
    else:
        raise ClaripyOperationError("unrecognized float sort")

    try:
        packed = struct.pack('<' + pack, concatted.value)
        unpacked, = struct.unpack('<' + unpack, packed)
    except OverflowError as e:
        # struct.pack sometimes overflows
        raise ClaripyOperationError("OverflowError: " + str(e))

    return FPV(unpacked, sort)

def fpToSBV(rm, fp, size):
    """
    Converts a backend FPV to a signed BVV taking rounding into account.

    :param rm: Rounding mode.
    :param fp: Backend FPV to convert.
    :param size: Size of BVV to create.

    :returns: Takes the floating point value and casts to the appropriate int,
              and returns a BVV with the correct value. On ValueError or
              OverflowError returns a BVV containing the value 0.
    :raises: ClaripyOperationError
    """
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
    """
    Converts a backend FPV to an unsigned BVV taking rounding into account.

    :param rm: Rounding mode.
    :param fp: Backend FPV to convert.
    :param size: Size of BVV to create.

    :returns: Currently the same as fpToSBV, unsigned conversion is not yet
              implemented.
    :raises: ClaripyOperationError
    """
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
    """
    Test equality of backend FPVs `a` and `b`.
    """
    return a == b

def fpNE(a, b):
    """
    Test inequality of backend FPVs `a` and `b`.
    """
    return a != b

def fpGT(a, b):
    """
    Test if backend FPV `a` > `b`.
    """
    return a > b

def fpGEQ(a, b):
    """
    Test if backend FPV `a` >= `b`.
    """
    return a >= b

def fpLT(a, b):
    """
    Test if backend FPV `a` < `b`.
    """
    return a < b

def fpLEQ(a, b):
    """
    Test if backend FPV `a` <= `b`.
    """
    return a <= b

def fpAbs(x):
    """
    Computes the absolute value of backend FPV `x`.
    """
    return abs(x)

def fpNeg(x):
    """
    Computes the negation of backend FPV `x`.
    """
    return -x

def fpSub(_rm, a, b):
    """
    Computes the difference `a` - `b` of backend FPVs.
    """
    return a - b

def fpAdd(_rm, a, b):
    """
    Computes the sum `a` + `b` of backend FPVs.
    """
    return a + b

def fpMul(_rm, a, b):
    """
    Computes the product `a` * `b` of backend FPVs.
    """
    return a * b

def fpDiv(_rm, a, b):
    """
    Computes the division `a` / `b` of backend FPVs.
    """
    return a / b

from .bv import BVV, Concat
