from .bits import Bits
from ..ast.base import Base, _make_name

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

def FPI(model, **kwargs):
    kwargs['length'] = model.sort.length
    return FP('I', (model,), **kwargs)

def FloatingPoint(name, sort, explicit_name=None):
    n = _make_name(name, sort.length, explicit_name=explicit_name, prefix='FP_')
    return FP('FP', (n, sort), variables={n}, symbolic=True, simplified=Base.FULL_SIMPLIFY, length=sort.length)

def FPV(*args):
    return FPI(fp.FPV(*args), variables=set(), symbolic=False, simplified=Base.FULL_SIMPLIFY, eager=True)

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

fpToFP = operations.op('fpToFP', object, FP, bound=False, calc_length=_fp_length_calc)
fpToFPUnsigned = operations.op('fpToFPUnsigned', (fp.RM, BV, fp.FSort), FP, bound=False, calc_length=_fp_length_calc)
fpFP = operations.op('fpFP', (BV, BV, BV), FP, bound=False,
                  calc_length=lambda a, b, c: a.length + b.length + c.length)
fpToIEEEBV = operations.op('fpToIEEEBV', (FP,), BV, bound=False, calc_length=lambda fp: fp.length)
fpToSBV = operations.op('fpToSBV', (fp.RM, FP, (int, long)), BV, bound=False, calc_length=lambda _rm, _fp, len: len)
fpToUBV = operations.op('fpToUBV', (fp.RM, FP, (int, long)), BV, bound=False, calc_length=lambda _rm, _fp, len: len)

#
# unbound float point comparisons
#

def _fp_cmp_check(a, b):
    return a.length == b.length, "FP lengths must be the same"
fpEQ = operations.op('fpEQ', (FP, FP), Bool, bound=False, extra_check=_fp_cmp_check)
fpGT = operations.op('fpGT', (FP, FP), Bool, bound=False, extra_check=_fp_cmp_check)
fpGEQ = operations.op('fpGEQ', (FP, FP), Bool, bound=False, extra_check=_fp_cmp_check)
fpLT = operations.op('fpLT', (FP, FP), Bool, bound=False, extra_check=_fp_cmp_check)
fpLEQ = operations.op('fpLEQ', (FP, FP), Bool, bound=False, extra_check=_fp_cmp_check)

#
# unbound floating point arithmetic
#

def _fp_binop_check(rm, a, b): #pylint:disable=unused-argument
    return a.length == b.length, "Lengths must be equal"
def _fp_binop_length(rm, a, b): #pylint:disable=unused-argument
    return a.length
fpAbs = operations.op('fpAbs', (FP,), FP, bound=False, calc_length=lambda x: x.length)
fpNeg = operations.op('fpNeg', (FP,), FP, bound=False, calc_length=lambda x: x.length)
fpSub = operations.op('fpSub', (fp.RM, FP, FP), FP, bound=False, extra_check=_fp_binop_check, calc_length=_fp_binop_length)
fpAdd = operations.op('fpAdd', (fp.RM, FP, FP), FP, bound=False, extra_check=_fp_binop_check, calc_length=_fp_binop_length)
fpMul = operations.op('fpMul', (fp.RM, FP, FP), FP, bound=False, extra_check=_fp_binop_check, calc_length=_fp_binop_length)
fpDiv = operations.op('fpDiv', (fp.RM, FP, FP), FP, bound=False, extra_check=_fp_binop_check, calc_length=_fp_binop_length)

#
# bound fp operations
#
fp.__eq__ = operations.op('fpEQ', (FP, FP), Bool, extra_check=_fp_cmp_check)
