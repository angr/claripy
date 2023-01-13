import struct

from .bits import Bits
from ..ast.base import _make_name
from ..fp import FSORT_FLOAT


class FP(Bits):
    """
    An AST representing a set of operations culminating in an IEEE754 floating point number.

    Do not instantiate this class directly, instead use FPV or FPS to construct a value or symbol, and then use
    operations to construct more complicated expressions.

    :ivar length:   The length of this value
    :ivar sort:     The sort of this value, usually either FSORT_FLOAT or FSORT_DOUBLE
    """

    __slots__ = ()

    def to_fp(self, sort, rm=None):
        """
        Convert this float to a different sort

        :param sort:    The sort to convert to
        :param rm:      Optional: The rounding mode to use
        :return:        An FP AST
        """
        if rm is None:
            rm = fp.RM.default()

        return fpToFP(rm, self, sort)

    def raw_to_fp(self):
        """
        A counterpart to BV.raw_to_fp - does nothing and returns itself.
        """
        return self

    def raw_to_bv(self):
        """
        Interpret the bit-pattern of this IEEE754 floating point number as a bitvector.
        The inverse of this function is to_bv.

        :return:        A BV AST whose bit-pattern is the same as this FP
        """
        return fpToIEEEBV(self)

    def to_bv(self):
        return self.raw_to_bv()

    def val_to_bv(self, size, signed=True, rm=None):
        """
        Convert this floating point value to an integer.

        :param size:    The size of the bitvector to return
        :param signed:  Optional: Whether the target integer is signed
        :param rm:      Optional: The rounding mode to use
        :return:        A bitvector whose value is the rounded version of this FP's value
        """
        if rm is None:
            rm = fp.RM.default()

        op = fpToSBV if signed else fpToUBV
        return op(rm, self, size)

    @property
    def sort(self):
        return fp.FSort.from_size(self.length)

    @staticmethod
    def _from_float(like, value):
        return FPV(float(value), like.sort)

    _from_int = _from_float
    _from_str = _from_float


def FPS(name, sort, explicit_name=None):
    """
    Creates a floating-point symbol.

    :param name:            The name of the symbol
    :param sort:            The sort of the floating point
    :param explicit_name:   If False, an identifier is appended to the name to ensure uniqueness.
    :return:                An FP AST.
    """

    n = _make_name(name, sort.length, False if explicit_name is None else explicit_name, prefix="FP_")
    return FP("FPS", (n, sort), variables={n}, symbolic=True, length=sort.length)


def FPV(value, sort):
    """
    Creates a concrete floating-point value.

    :param value:   The value of the floating point.
    :param sort:    The sort of the floating point.
    :return:        An FP AST.
    """
    if type(value) is int:
        value = float(value)
    elif type(value) is float:
        pass
    else:
        raise TypeError("Must instanciate FPV with a numerical value")

    if type(sort) is not fp.FSort:
        raise TypeError("Must instanciate FPV with a FSort")

    if sort == FSORT_FLOAT:
        # By default, Python treats all floating-point numbers as double-precision. However, a single-precision float is
        # being created here. Hence, we need to convert value to single-precision.
        value = struct.unpack("f", struct.pack("f", value))[0]

    return FP("FPV", (value, sort), length=sort.length)


#
# unbound floating point conversions
#

from .. import operations
from .. import fp
from .bv import BV
from .bool import Bool


def _fp_length_calc(a1, a2, a3=None):
    if isinstance(a1, fp.RM) and a3 is None:
        raise Exception()
    if a3 is None:
        return a2.length
    else:
        return a3.length


fpToFP = operations.op("fpToFP", object, FP, bound=False, calc_length=_fp_length_calc)
fpToFPUnsigned = operations.op("fpToFPUnsigned", (fp.RM, BV, fp.FSort), FP, bound=False, calc_length=_fp_length_calc)
fpFP = operations.op("fpFP", (BV, BV, BV), FP, bound=False, calc_length=lambda a, b, c: a.length + b.length + c.length)
fpToIEEEBV = operations.op("fpToIEEEBV", (FP,), BV, bound=False, calc_length=lambda fp: fp.length)
fpToSBV = operations.op("fpToSBV", (fp.RM, FP, int), BV, bound=False, calc_length=lambda _rm, _fp, len: len)
fpToUBV = operations.op("fpToUBV", (fp.RM, FP, int), BV, bound=False, calc_length=lambda _rm, _fp, len: len)

#
# unbound float point comparisons
#


def _fp_cmp_check(a, b):
    return a.length == b.length, "FP lengths must be the same"


fpEQ = operations.op("fpEQ", (FP, FP), Bool, bound=False, extra_check=_fp_cmp_check)
fpGT = operations.op("fpGT", (FP, FP), Bool, bound=False, extra_check=_fp_cmp_check)
fpGEQ = operations.op("fpGEQ", (FP, FP), Bool, bound=False, extra_check=_fp_cmp_check)
fpLT = operations.op("fpLT", (FP, FP), Bool, bound=False, extra_check=_fp_cmp_check)
fpLEQ = operations.op("fpLEQ", (FP, FP), Bool, bound=False, extra_check=_fp_cmp_check)
fpIsNaN = operations.op("fpIsNaN", (FP,), Bool, bound=False)
fpIsInf = operations.op("fpIsInf", (FP,), Bool, bound=False)

#
# unbound floating point arithmetic
#


def _fp_binop_check(rm, a, b):  # pylint:disable=unused-argument
    return a.length == b.length, "Lengths must be equal"


def _fp_binop_length(rm, a, b):  # pylint:disable=unused-argument
    return a.length


fpAbs = operations.op("fpAbs", (FP,), FP, bound=False, calc_length=lambda x: x.length)
fpNeg = operations.op("fpNeg", (FP,), FP, bound=False, calc_length=lambda x: x.length)
fpSub = operations.op(
    "fpSub", (fp.RM, FP, FP), FP, bound=False, extra_check=_fp_binop_check, calc_length=_fp_binop_length
)
fpAdd = operations.op(
    "fpAdd", (fp.RM, FP, FP), FP, bound=False, extra_check=_fp_binop_check, calc_length=_fp_binop_length
)
fpMul = operations.op(
    "fpMul", (fp.RM, FP, FP), FP, bound=False, extra_check=_fp_binop_check, calc_length=_fp_binop_length
)
fpDiv = operations.op(
    "fpDiv", (fp.RM, FP, FP), FP, bound=False, extra_check=_fp_binop_check, calc_length=_fp_binop_length
)
fpSqrt = operations.op(
    "fpSqrt",
    (
        fp.RM,
        FP,
    ),
    FP,
    bound=False,
    calc_length=lambda _, x: x.length,
)

#
# bound fp operations
#

FP.__eq__ = operations.op("fpEQ", (FP, FP), Bool, extra_check=_fp_cmp_check)
FP.__ne__ = operations.op("fpNE", (FP, FP), Bool, extra_check=_fp_cmp_check)
FP.__ge__ = operations.op("fpGEQ", (FP, FP), Bool, extra_check=_fp_cmp_check)
FP.__le__ = operations.op("fpLEQ", (FP, FP), Bool, extra_check=_fp_cmp_check)
FP.__gt__ = operations.op("fpGT", (FP, FP), Bool, extra_check=_fp_cmp_check)
FP.__lt__ = operations.op("fpLT", (FP, FP), Bool, extra_check=_fp_cmp_check)

FP.__abs__ = fpAbs
FP.__neg__ = fpNeg

FP.__add__ = fpAdd
FP.__sub__ = fpSub
FP.__mul__ = fpMul
FP.__truediv__ = fpDiv
FP.Sqrt = fpSqrt

FP.__radd__ = operations.reversed_op(FP.__add__)
FP.__rsub__ = operations.reversed_op(FP.__sub__)
FP.__rmul__ = operations.reversed_op(FP.__mul__)
FP.__rtruediv__ = operations.reversed_op(FP.__truediv__)

FP.isNaN = fpIsNaN
FP.isInf = fpIsInf
