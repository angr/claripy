"""
Define a function used to generate the .args of a claripy AST
"""
from typing import Type, Tuple, List, Dict, Any

from .data_types import LegacyData
from .fp import rm_cpp_to_py, width_cpp_to_py

from ..load import clari
from ...fp import FSORT_DOUBLE, FSORT_FLOAT

_cmfp = clari.Mode.FP  ## Cache this dict search for speed

def _to_py_arg(x: Any, children: Dict[int, "claripy.ast.Base"]) -> Any:
    """
    Convert the native object to the .args python object which represents it
    """
    if isinstance(x, clari.Expr.Base):
        return children[hash(x)]
    elif isinstance(x, clari.BigInt):
        return int(x.value)
    elif isinstance(x, _cmfp.Rounding):
        return rm_cpp_to_py[x]
    elif isinstance(x, _cmfp.Width):
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
    Generate the .args list; note this can be very expensive
    :param op: The python op name
    :param uninitialized: The _uninitialized field of a clairpy expr
    :param native: The native object to extract args from (get from py_expr._native)
    :param legacy: The LegacyData associated with the native object (get from py_expr._legacy)
    """
    cpp: List[Any] = native.op.python_children()
    # Fix specific ops
    if op in {"FPV", "FPS"}:
        # We only have a length b/c claripy FPV/FPS only hold total lengths
        cpp.append(FSORT_DOUBLE if len(native) == 64 else FSORT_FLOAT)
    elif op in {"BVV", "StringV", "VSV", "StrIndexOf", "fpToUBV"}:
        cpp.append(len(native))
    elif op == "StringS":
        cpp.append(uninitialized)
    if op == "BVS":
        cpp.extend(legacy.bvs)
    elif op in {"ZeroExt", "SignExt"}:
        cpp = cpp[::-1]
    elif op == "StringV":
        cpp[1] /= 8
    # Convert a C++ arg to python
    exprs = legacy.exprs
    ret: Tuple[Any] = tuple(_to_py_arg(i, exprs) for i in cpp)
    # TODO: delete this section; it just verifies .args was created properly
    if not _chk_eq_args(ret, legacy.py_args):
        print("Diff args!")
        print("Python: legacy.py_args")
        print("Native: ret")
        import IPython
        IPython.embed()
    return ret

__all__ = ("args",)
