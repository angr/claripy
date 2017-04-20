from .bits import Bits
from ..ast.base import _make_name, make_op

class FP(Bits):
    def to_fp(self, rm, sort):
        if rm is None:
            rm = fp.RM.default()

        return fpToFP(rm, self, sort)

    def raw_to_fp(self):
        return self

    def to_bv(self):
        return fpToIEEEBV(self)

    @property
    def sort(self):
        return fp.FSort.from_size(self.length)

def FPS(name, sort, explicit_name=None, filters=None):
    """
    Creates a floating-point symbol.

    :param name:            The name of the symbol
    :param sort:            The sort of the floating point
    :param explicit_name:   If False, an identifier is appended to the name to ensure uniqueness.
    :return:                An FP AST.
    """

    n = _make_name(name, sort.length, False if explicit_name is None else explicit_name, prefix='FP_')
    return FP(get_structure('FPS', (n, sort)), filters=filters, _eager=False)._deduplicate()._apply_filters()

def FPV(value, sort, filters=None):
    """
    Creates a concrete floating-point value.

    :param value:   The value of the floating point.
    :param sort:    The sort of the floating point.
    :return:        An FP AST.
    """
    return FP(get_structure('FPV', (value, sort)), filters=filters)._deduplicate()._apply_filters()

#
# unbound floating point conversions
#

from .. import fp
from .bv import BV
from .bool import Bool
from .structure import get_structure

fpToFP = make_op('fpToFP', object, FP)
fpToFPUnsigned = make_op('fpToFPUnsigned', (fp.RM, BV, fp.FSort), FP)
fpFP = make_op('fpFP', (BV, BV, BV), FP)
fpToIEEEBV = make_op('fpToIEEEBV', (FP,), BV)
fpToSBV = make_op('fpToSBV', (fp.RM, FP, (int, long)), BV)
fpToUBV = make_op('fpToUBV', (fp.RM, FP, (int, long)), BV)

#
# unbound float point comparisons
#

fpEQ = make_op('fpEQ', (FP, FP), Bool)
fpGT = make_op('fpGT', (FP, FP), Bool)
fpGEQ = make_op('fpGEQ', (FP, FP), Bool)
fpLT = make_op('fpLT', (FP, FP), Bool)
fpLEQ = make_op('fpLEQ', (FP, FP), Bool)

#
# unbound floating point arithmetic
#

fpAbs = make_op('fpAbs', (FP,), FP)
fpNeg = make_op('fpNeg', (FP,), FP)
fpSub = make_op('fpSub', (fp.RM, FP, FP), FP)
fpAdd = make_op('fpAdd', (fp.RM, FP, FP), FP)
fpMul = make_op('fpMul', (fp.RM, FP, FP), FP)
fpDiv = make_op('fpDiv', (fp.RM, FP, FP), FP)

#
# bound fp operations
#
FP.__eq__ = make_op('fpEQ', (FP, FP), Bool)
FP.__ne__ = make_op('fpNE', (FP, FP), Bool)
FP.__ge__ = make_op('fpGEQ', (FP, FP), Bool)
FP.__le__ = make_op('fpLEQ', (FP, FP), Bool)
FP.__gt__ = make_op('fpGT', (FP, FP), Bool)
FP.__lt__ = make_op('fpLT', (FP, FP), Bool)
