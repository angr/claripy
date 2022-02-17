# TODO: prefer CUIDs to string IDs

"""
py_leaves = frozenset([
    'bool_s',
    'string_s',
    'bv_s',
    'fp_s',
    'vs_s',
    'bv_v',
    'bool_v',
    'fp_v',
    'string_v',
    'vs_v'
])
"""

''' TODO
class PyOp(enum.Enum):
    """
    An enum of python ops
    """
    # Leaves
    # Non-leaves
    if_ = enum.auto()
    extract = enum.auto()
    abs_ = enum.auto()
    neg = enum.auto()
    not_ = enum.auto()
    invert = enum.auto()
    reverse = enum.auto()
    sign_ext = enum.auto()
    zero_ext = enum.auto()
    eq = enum.auto()
    neq = enum.auto()
    slt = enum.auto()
    sle = enum.auto()
    sgt = enum.auto()
    sge = enum.auto()
    ult = enum.auto()
    ule = enum.auto()
    ugt = enum.auto()
    uge = enum.auto()
    sub = enum.auto()
    sdiv = enum.auto()
    udiv = enum.auto()
    smod = enum.auto()
    umod = enum.auto()
    shl = enum.auto()
    shlr = enum.auto()
    shar = enum.auto()
    widen = enum.auto()
    union = enum.auto()
    intersection = enum.auto()
    concat = enum.auto()
    add = enum.auto()
    mul = enum.auto()
    or_ = enum.auto()
    and_ = enum.auto()
    xor = enum.auto()
    to_ieee_bv = enum.auto()
    fp_add = enum.auto()
    fp_sub = enum.auto()
    fp_mul = enum.auto()
    fp_div = enum.auto()
    fp = enum.auto()

py_leaves = frozenset([ PyOp.Symbol, PyOp.Literal ])
'''

# A map from C++ types to python types
# Maps a PyOp to either a tuple(type name, op name, extra) or just to an op name
# If it maps to a tuple, entries may be none if not applicable
cpp_to_py = {
    ("Bool", "Symbol"): "BoolS",
    ("String", "Symbol"): "StringS",
    ("BV", "Symbol"): "BVS",
    ("FP", "Symbol"): "FPS",
    ("VS", "Symbol"): "VSS",
    ("Bool", "Literal"): "BoolV",
    ("String", "Literal"): "StringV",
    ("BV", "Literal"): "BVV",
    ("FP", "Literal"): "FPV",
    ("VS", "Literal"): "VSV",
    "If": "If",
    "Extract": "Extract",
    "Abs": "__abs__",
    "Neg": "__neg__",
    "Not": "Not",
    "Invert": "__invert__",
    "Reverse": "Reverse",
    "SignExt": "SignExt",
    "ZeroExt": "ZeroExt",
    "Eq": "__eq__",
    "Neq": "__neq__",
    "Compare-Signed-Less-Neq": "SLT",
    "Compare-Signed-Less-Eq": "SLE",
    "Compare-Signed-Greater-Neq": "SGT",
    "Compare-Signed-Greater-Eq": "SGE",
    "Compare-Unsigned-Less-Neq": "ULT",
    "Compare-Unsigned-Less-Eq": "ULE",
    "Compare-Unsigned-Greater-Neq": "UGT",
    "Compare-Unsigned-Greater-Eq": "UGE",
    # "Compare-Unsigned-Less-Neq": "__lt__",
    # "Compare-Unsigned-Less-Eq": "__le__",
    # "Compare-Unsigned-Greater-Neq": "__gt__",
    # "Compare-Unsigned-Greater-Eq": "__ge__",
    "Sub": "__sub__",
    "Div-Signed": "SDiv",
    "Div-Unsigned": "__floordiv__",
    "Mod-Signed": "SMod",
    "Mod-Unsigned": "__mod__",
    "Shift-Left": "__lshift__",
    "Shift-Logical-Right": "LShR",
    "Shift-Arithmetic-Right": "__rshift__",
    "Widen": "widen",
    "Union": "union",
    "Intersection": "intersection",
    "Concat": "Concat",
    "Add": "__add__",
    "Mul": "__mul__",
    "Or": "__or__",
    "And": "__and__",
    "Xor": "__xor__",
    # FP
    "FP::ToIEEEBV": "to_ieee_bv",
    "FP::Add": "fp_add",
    "FP::Sub": "fp_sub",
    "FP::Mul": "fp_mul",
    "FP::Div": "fp_div",
    "FP::Fp": "fp",
    # String
    "String::FromInt": "IntToStr",
    "String::IndexOf": "StrIndexOf",
    "String::Replace": "StrReplace",
    "String::SubStr": "StrSubStr",
    "String::IsDigit": "StrIsDigit",
    "String::ToInt": "StrToInt",
    "String::Len": "StrLen",
    "String::Contains": "StrContains",
    "String::PrefixOf": "StrPrefixOf",
    "String::SuffixOf": "StrSuffixOf",
}
