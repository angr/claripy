from typing import Type, List, Dict, Any

from .data_types import LegacyData
from .fp import rm_cpp_to_py, width_cpp_to_py

from ..load import clari
from ...fp import FSORT_DOUBLE, FSORT_FLOAT


def _to_py_arg(x: Any, children: Dict[int, "claripy.ast.Base"]) -> Any:
    """
    Convert the native object to the .args python object which represents it
    """
    if isinstance(x, clari.Expr.Base):
        return children[hash(x)]
    elif isinstance(x, clari.Mode.FP.Rounding):
        return rm_cpp_to_py[x]
    elif isinstance(x, clari.Mode.FP.Width):
        return width_cpp_to_py(x)
    return x

def _chk_eq_args(a: List[Any], b: List[Any]) -> bool:  # TODO: remove when not debugging
    """
    Verify the cpp args were generated properly (they should be the same as the python args)
    TODO: THIS METHOD SHOULD BE DELETED
    """
    if len(a) == len(b):
        for i in range(len(a)):
            if hash(a[i]) != hash(b[i]):
                return False
    return True

def args(op: str, uninitialized: bool, native: Type[clari.Expr.Base], legacy: LegacyData) -> List[Any]:
    """
    :param op: The python op name
    :param uninitialized: The _uninitialized field of a clairpy expr
    :param native: The native object to extract args from (get from py_expr._native)
    :param legacy: The LegacyData associated with the native object (get from py_expr._legacy)
    Generate the legacy .args from the native object
    """
    na: List[Any] = list(native.args)
    # Fix specific ops
    if op in {"FPV", "FPS"}:
        # We only have a length b/c claripy FPV/FPS only hold total lengths
        na.append(FSORT_DOUBLE if len(native) == 64 else FSORT_FLOAT)
    elif op in {"BVV", "StringV", "VSV", "StrIndexOf", "fpToUBV"}:
        na.append(len(native))
    elif op == "StringS":
        na.append(uninitialized)
    if op == "BVS":
        na.extend(legacy.bvs)
    elif op in {"ZeroExt", "SignExt"}:
        na = na[::-1]
    elif op == "StringV":
        na[1] /= 8
    # Convert a C++ arg to python
    exprs = legacy.exprs
    ret: List[Any] = tuple([_to_py_arg(i, exprs) for i in na])
    # TODO: delete this section; it just verifies .args was created properly
    if not _chk_eq_args(ret, legacy.py_args):
        print("Diff args!")
        print("Python: legacy._py_args")
        print("Native: ret")
        import IPython
        IPython.embed()
    return ret

__all__ = ("args",)
