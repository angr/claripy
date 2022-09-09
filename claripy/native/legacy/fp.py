from typing import Dict

from ..load import clari
from ...fp import RM, FSort, FSORT_FLOAT, FSORT_DOUBLE


_Rounding: type = clari.Mode.FP.Rounding
_rms = (
    (RM.RM_TowardsZero, _Rounding.TowardsZero,),
    (RM.RM_NearestTiesEven, _Rounding.NearestTiesEven,),
    (RM.RM_TowardsPositiveInf, _Rounding.TowardsPositiveInf,),
    (RM.RM_TowardsNegativeInf, _Rounding.TowardsNegativeInf,),
    (RM.RM_NearestTiesAwayFromZero, _Rounding.NearestTiesAwayFromZero,),
)
_cpp_flt: _Rounding = clari.Mode.FP.flt
_cpp_dbl: _Rounding = clari.Mode.FP.dbl


# Exports


# Maps between python and C++ rounding modes
rm_py_to_cpp: Dict[FSort, _Rounding] = { i:k for i,k in _rms }
rm_cpp_to_py: Dict[_Rounding, FSort] = { k:i for i,k in _rms }


def width_py_to_cpp(x: FSort) -> clari.Mode.FP.Width:
    """
    Convert a python FP Width to a C++ Width
    """
    if x == FSORT_DOUBLE:
        return _cpp_dbl
    elif x == FSORT_FLOAT:
        return _cpp_flt
    raise RuntimeError(f"Unsupported float width: {x}")


def width_cpp_to_py(x: clari.Mode.FP.Width) -> FSort:
    """
    Convert a python FP Width to a C++ Width
    """
    if x == _cpp_dbl:
        return FSORT_DOUBLE
    elif x == _cpp_flt:
        return FSORT_FLOAT
    raise RuntimeError(f"Unsupported float width: {x}")


__all__ = ("rm_py_to_cpp", "rm_cpp_to_py", "width_py_to_cpp", "width_cpp_to_py")
