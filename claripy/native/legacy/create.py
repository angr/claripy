from typing import List, Optional, Any, Dict, Tuple, Callable

from .data_types import LegacyData
from .fp import rm_py_to_cpp, width_py_to_cpp

from ..load import clari
from ...fp import FSort, RM


_op_ctor_type = None  ## A cache so we only build this once


def _BVV(val: int, bit_length: int, annotations: Optional[List] = None):
    """
    A BVV ctor
    """
    val %= (2**bit_length) # TODO: maybe move to C++?
    if val >= 2**64:
        val = str(val)
    return clari.Create.literal_bv(val, bit_length, annotations)

def _ctor_type(op: str):
    """
    Return a C++ ctor/type given a python op name
    Warning: This error if this op cannot be simply mapped
    """
    global _op_ctor_type
    if _op_ctor_type is not None:
        return _op_ctor_type[op]
    C = clari.Create
    O = clari.Op
    _op_ctor_type = {
        "BoolV": (C.literal_bool, O.Literal),
        "BVV": (_BVV, O.Literal),
        "Extract": (C.extract, O.Extract),
        "FPV": (C.literal_fp, O.Literal),
        "StringV": (C.literal_string, O.Literal),
        "StringS": (C.symbol_string, O.Symbol),
        "StrConcat": (C.concat, O.Concat),
        "__eq__": (C.eq, O.Eq),
        "StrContains": (C.String.contains, O.String.Contains),
        "StrIndexOf": (C.String.index_of, O.String.IndexOf),
        "BVS": (C.symbol_bv, O.Symbol),
        "__gt__": (C.ugt, O.UGT),
        "__lt__": (C.ult, O.ULT),
        "__ne__": (C.neq, O.Neq),
        "IntToStr": (C.String.from_int, O.String.FromInt),
        "StrIsDigit": (C.String.is_digit, O.String.IsDigit),
        "StrLen": (C.String.len, O.String.Len),
        "__le__": (C.ule, O.ULE),
        "__ge__": (C.uge, O.UGE),
        "Or": (C.or_, O.Or),
        "StrPrefixOf": (C.String.prefix_of, O.String.PrefixOf),
        "StrReplace": (C.String.replace, O.String.Replace),
        "StrToInt": (C.String.to_int, O.String.ToInt),
        "StrSubstr": (C.String.sub_string, O.String.SubString),
        "StrSuffixOf": (C.String.suffix_of, O.String.SuffixOf),
        "__add__": (C.add, O.Add),
        "__rshift__": (C.shift_arithmetic_right, O.ShiftArithmeticRight),
        "BoolS": (C.symbol_bool, O.Symbol),
        "And": (C.and_, O.And),
        "__mul__": (C.mul, O.Mul),
        "If": (C.if_, O.If),
        "union": (C.union_, O.Union),
        "intersection": (C.intersection_, O.Intersection),
        "LShR": (C.shift_logical_right, O.ShiftLogicalRight),
        "Reverse": (C.reverse, O.Reverse),
        "ZeroExt": (C.zero_ext, O.ZeroExt),
        "SignExt": (C.sign_ext, O.SignExt),
        "Concat": (C.concat, O.Concat),
        "__mod__": (C.mod_unsigned, O.ModUnsigned),
        "__sub__": (C.sub, O.Sub),
        "__or__": (C.or_, O.Or),
        "__xor__": (C.xor_, O.Xor),
        "__and__": (C.and_, O.And),
        "__floordiv__": (C.div_unsigned, O.DivUnsigned),
        "SDiv": (C.div_signed, O.DivSigned),
        "SMod": (C.mod_signed, O.ModSigned),
        "ULE": (C.ule, O.ULE),
        "Not": (C.not_, O.Not),
        "__lshift__": (C.shift_l, O.ShiftLeft),
        "fpToUBV": (C.FP.to_bv_unsigned, O.FP.ToBVUnsigned),
        "FPS": (C.symbol_fp, O.Symbol),
        "fpEQ": (C.eq, O.Eq),
        "fpAbs": (C.abs, O.Abs),
        "fpAdd": (C.FP.add, O.FP.Add),
        "fpSub": (C.FP.sub, O.FP.Sub),
        "fpMul": (C.FP.mul, O.FP.Mul),
        "fpDiv": (C.FP.div, O.FP.Div),
        "fpIsNaN": (C.FP.is_nan, O.FP.IsNan),
        "fpToIEEEBV": (C.FP.to_ieee_bv, O.FP.ToIEEEBV),
        "__invert__": (C.invert, O.Invert),
        "SLT": (C.slt, O.SLT),
        "SGE": (C.sge, O.SGE),
        "SLE": (C.sle, O.SLE),
        "widen": (C.widen, O.Widen),
    }
    return _ctor_type(op)

def _to_cpp_arg(arg: Any) -> Any:
    """
    Convert a python argument to a claricpp argument
    """
    try:
        return arg._native  # TODO: no hasattr check b/c @property is weird
    except AttributeError:
        if isinstance(arg, FSort):
            return width_py_to_cpp(arg)
        elif isinstance(arg, RM):
            return rm_py_to_cpp[arg]
        return arg

def _ctor_args(op: str, cpp_type: type, py_args: List[Any], length: Optional[int]) -> List[Any]:
    """
    Convert python arguments to args for the clari ctor for the given op
    """
    # Special cases
    if op == "BoolS":
        return (py_args[0],)
    elif op in {'BVS', 'FPS', 'FPV', 'VSS', 'StringS'}:
        assert length is not None, f"{op} should have a length"
        return (py_args[0], length)
    # Fix and order args
    args: List[Any] = [_to_cpp_arg(i) for i in py_args]
    if issubclass(cpp_type, clari.Op.AbstractFlat):
        return (args,)
    elif issubclass(cpp_type, clari.Op.UIntBinary) and not op.startswith("Str"):
        return args[::-1]
    elif issubclass(cpp_type, clari.Op.FP.ModeBinary):
        return args[1:] + [args[0]]
    return args


def create(base: type, op: str, py_args: List[Any],
           length: Optional[int], other: Dict[str, Any]) -> Tuple[clari.Expr.Base, LegacyData]:
    """
    Create a claricpp object with op type op and py_args as arguments
    Length is passed if the object is sized
    Note: This expects claripy ops in py_args define both ._native
    and ._legacy using values gotten from calling this method
    :param base: The base claripy AST type (used for checking of .args[i] is a claripy AST)
    :param op: The claripy op
    :param py_args: The op arguments
    :param length: The length argument passed to claripy.ast.base's __init__ function
    :return: The native op & a data object needed for legacy support
    """
    # Determine the op constructor / type
    ctor: Callable
    cpp_type: type
    if op == "fpToFP":
        if len(py_args) == 2:
            ctor = clari.Create.FP.from_not_2s_complement_bv
            cpp_type = clari.Op.FP.FromNot2sComplementBV
        elif hasattr(py_args[1], 'sort'):
            ctor = clari.Create.FP.from_fp
            cpp_type = clari.Op.FP.FromFP
        else:
            ctor = clari.Create.FP.from_2s_complement_signed
            cpp_type = clari.Op.FP.From2sComplementSigned
    else:
        ctor, cpp_type = _ctor_type(op)
    # Construct native and legacy
    native: clari.Expr.Base = ctor(*_ctor_args(op, cpp_type, py_args, length), other)
    return native, LegacyData(
        exprs={hash(i._native):i for i in py_args if isinstance(i, base)},
        bvs=(py_args[1:] if op == "BVS" else None),
        py_args=tuple(py_args),
    )


__all__ = ("create",)
