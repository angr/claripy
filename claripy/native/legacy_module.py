from .clari_setup import clari

from enum import Enum


class _Wrapper:
    """
    Wrappers for clari creation methods to bring them more inline with claripy
    """
    @staticmethod
    def BVV(val, bit_length, annotations=None):
        val %= (2**bit_length) # TODO: maybe move to C++?
        if val >= 2**64:
            val = str(val)
        return clari.Create.literal_bv(val, bit_length, annotations)
    @staticmethod
    def StringV(s, size):
        return clari.Create.literal_string(s.ljust(size, "\0"))
    @staticmethod
    def union(*args):
        return clari.Create.union_(*(args[0] if len(args) == 1 else args))
    # TODO: ^ check with fish


### Helpers


def _bimap(*x):
    return {i: k for i, k in x}, {k: i for i, k in x},

def _fix_arg(arg):
    try:
        return arg._native  # TODO: no hasattr check b/c @property is weird
    except AttributeError:
        if isinstance(arg, Enum):
            return conv_rm(arg.value)
        return arg

def _from_py_args(op, t, py_args, length):
    # Special cases
    if op == "BoolS":
        return (py_args[0],)
    elif op in {'BVS', 'FPS', 'FPV', 'VSS', 'StringS'}:
        assert length is not None, f"{op} should have a length"
        return (py_args[0], length,)
    # Fix and order args
    args = [_fix_arg(i) for i in py_args]
    if issubclass(t, clari.Op.AbstractFlat):
        return (args,)
    elif issubclass(t, clari.Op.UIntBinary) and not op.startswith("Str"):
        return args[::-1]
    elif issubclass(t, clari.Op.FP.ModeBinary):
        return args[1:] + [args[0]]
    return args


### Generate maps


# Note: we do not make things on import!
# LegacySetup may change functions!
# We instead expose an init function

def _gen_op_ctor_type():
    C = clari.Create
    O = clari.Op
    return {
        "BoolV": (C.literal_bool, O.Literal,),
        "BVV": (_Wrapper.BVV, O.Literal,),
        "Extract": (C.extract, O.Extract,),
        "FPV": (C.literal_fp, O.Literal,),
        "StringV": (_Wrapper.StringV, O.Literal,),
        "StringS": (C.symbol_string, O.Symbol,),
        "StrConcat": (C.concat, O.Concat,),
        "__eq__": (C.eq, O.Eq,),
        "StrContains": (C.String.contains, O.String.Contains,),
        "StrIndexOf": (C.String.index_of, O.String.IndexOf,),
        "BVS": (C.symbol_bv, O.Symbol,),
        "__gt__": (C.ugt, O.UGT,),
        "__lt__": (C.ult, O.ULT,),
        "__ne__": (C.neq, O.Neq,),
        "IntToStr": (C.String.from_int, O.String.FromInt,),
        "StrIsDigit": (C.String.is_digit, O.String.IsDigit,),
        "StrLen": (C.String.len, O.String.Len,),
        "__le__": (C.ule, O.ULE,),
        "__ge__": (C.uge, O.UGE,),
        "Or": (C.or_, O.Or,),
        "StrPrefixOf": (C.String.prefix_of, O.String.PrefixOf,),
        "StrReplace": (C.String.replace, O.String.Replace,),
        "StrToInt": (C.String.to_int, O.String.ToInt,),
        "StrSubstr": (C.String.sub_string, O.String.SubString,),
        "StrSuffixOf": (C.String.suffix_of, O.String.SuffixOf,),
        "__add__": (C.add, O.Add,),
        "__rshift__": (C.shift_arithmetic_right, O.ShiftArithmeticRight,),
        "BoolS": (C.symbol_bool, O.Symbol,),
        "And": (C.and_, O.And,),
        "__mul__": (C.mul, O.Mul,),
        "If": (C.if_, O.If,),
        "union": (_Wrapper.union, O.Union,),
        "intersection": (C.intersection_, O.Intersection,),
        "LShR": (C.shift_logical_right, O.ShiftLogicalRight,),
        "Reverse": (C.reverse, O.Reverse,),
        "ZeroExt": (C.zero_ext, O.ZeroExt,),
        "SignExt": (C.sign_ext, O.SignExt,),
        "Concat": (C.concat, O.Concat,),
        "__mod__": (C.mod_unsigned, O.ModUnsigned,),
        "__sub__": (C.sub, O.Sub,),
        "__or__": (C.or_, O.Or,),
        "__xor__": (C.xor_, O.Xor,),
        "__and__": (C.and_, O.And,),
        "__floordiv__": (C.div_unsigned, O.DivUnsigned,),
        "SDiv": (C.div_signed, O.DivSigned,),
        "SMod": (C.mod_signed, O.ModSigned,),
        "ULE": (C.ule, O.ULE,),
        "Not": (C.not_, O.Not,),
        "__lshift__": (C.shift_l, O.ShiftLeft,),
        "fpToUBV": (C.FP.to_bv_unsigned, O.FP.ToBVUnsigned,),
        "FPS": (C.symbol_fp, O.Symbol,),
        "fpAdd": (C.FP.add, O.FP.Add,),
        "fpIsNaN": (C.FP.is_nan, O.FP.IsNan,),
        "fpToIEEEBV": (C.FP.to_ieee_bv, O.FP.ToIEEEBV,),
        "__invert__": (C.invert, O.Invert,),
        "SLT": (C.slt, O.SLT,),
        "SGE": (C.sge, O.SGE,),
        "SLE": (C.sle, O.SLE,),
        "widen": (C.widen, O.Widen,),
    }

def _gen_rms():
    return _bimap(
        ('RM_RNE', clari.Mode.FP.Rounding.NearestTiesEven,),
        ('RM_RNA', clari.Mode.FP.Rounding.NearestTiesAwayFromZero,),
        ('RM_RTZ', clari.Mode.FP.Rounding.TowardsZero,),
        ('RM_RTP', clari.Mode.FP.Rounding.TowardsPositiveInf,),
        ('RM_RTN', clari.Mode.FP.Rounding.TowardsNegativeInf,),
    )

_op_ctor_type = None
_rms = None


### Exports


def init():
    global _rms
    _rms = _gen_rms()
    global _op_ctor_type
    _op_ctor_type = _gen_op_ctor_type()

def conv_rm(x):
    return _rms[1 if isinstance(x, clari.Mode.FP.Rounding) else 0][x]

def create(op, py_args, *, length=None):
    if op == "fpToFP":
        if len(py_args) == 2:
            ctor = clari.Create.FP.from_not_2s_complement_bv
            t = clari.Op.FP.FromNot2sComplementBV
        elif hasattr(py_args[1], 'sort'):
            ctor = clari.Create.FP.from_fp
            t = clari.Op.FP.FromFP
        else:
            ctor = clari.Create.FP.from_2s_complement_signed
            t = clari.Op.FP.From2sComplementSigned
    else:
        ctor, t = _op_ctor_type[op]
    return ctor(* _from_py_args(op, t, py_args, length))

__all__ = ("init", "create", "conv_rm",)