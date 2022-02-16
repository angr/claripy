from bidict import bidict

# TODO: prefer CUIDs to string IDs

'''
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
'''

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

# A map between python and C++ types
# Maps a PyOp to either a tuple(type name, op name, extra) or just to an op name
# If it maps to a tuple, entries may be none if not applicable
translations = bidict({
    "BoolS" : ("Bool", "Symbol"),
    "StringS" : ("String", "Symbol"),
    "BVS" : ("BV", "Symbol"),
    "FPS" : ("FP", "Symbol"),
    "VSS" : ("VS", "Symbol"),
    "BoolV" : ("Bool", "Literal"),
    "StringV" : ("String", "Literal"),
    "BVV" : ("BV", "Literal"),
    "FPV" : ("FP", "Literal"),
    "VSV" : ("VS", "Literal"),
    "If" : "If",
    "Extract" : "Extract",
    "__abs__" : "Abs",
    "__neg__" : "Neg",
    "Not" : "Not",
    "__invert__" : "Invert",
    "Reverse" : "Reverse",
    "SignExt" : "SignExt",
    "ZeroExt" : "ZeroExt",
    "__eq__" : "Eq",
    "__neq__" : "Neq",
    "SLT" : "Compare-Signed-Less-Neq",
    "SLE" : "Compare-Signed-Less-Eq",
    "SGT" : "Compare-Signed-Greater-Neq",
    "SGE" : "Compare-Signed-Greater-Eq",
    "ULT" : "Compare-Unsigned-Less-Neq",
    "ULE" : "Compare-Unsigned-Less-Eq",
    "UGT" : "Compare-Unsigned-Greater-Neq",
    "UGE" : "Compare-Unsigned-Greater-Eq",
    "__lt__" : "Compare-Unsigned-Less-Neq",
    "__le__" : "Compare-Unsigned-Less-Eq",
    "__gt__" : "Compare-Unsigned-Greater-Neq",
    "__ge__" : "Compare-Unsigned-Greater-Eq",
    "__sub__" : "Sub",
    "SDiv" : "Div-Signed",
    "__floordiv__" : "Div-Unsigned",
    "SMod" : "Mod-Signed",
    "__mod__" : "Mod-Unsigned",
    "__lshift__" : "Shift-Left",
    "LShR" : "Shift-Logical-Right",
    "__rshift__" : "Shift-Arithmetic-Right",
    "widen" : "Widen",
    "union" : "Union",
    "intersection" : "Intersection",
    "Concat" : "Concat",
    "__add__" : "Add",
    "__mul__" : "Mul",
    "__or__" : "Or",
    "__and__" : "And",
    "__xor__" :  "Xor",

    'to_ieee_bv' : "FP::ToIEEEBV",
    'fp_add' : "FP::Add",
    'fp_sub' : "FP::Sub",
    'fp_mul' : "FP::Mul",
    'fp_div' : "FP::Div",
    'fp' : "FP::Fp",

    "IntToStr" : "String::FromInt",
    "StrIndexOf" : "String::IndexOf",
    "StrReplace" : "String::Replace",
    "StrSubStr" : "String::SubStr",
    "StrIsDigit" : "String::IsDigit",
    "StrToInt" : "String::ToInt",
    "StrLen" : "String::Len",
    "StrContains" : "String::Contains",
    "StrPrefixOf" : "String::PrefixOf",
    "StrSuffixOf" : "String::SuffixOf",
})

# Sanity checks
for i, k in translations.items():
    assert type(i) is str, "Key should be a python op"
    if type(k) is tuple:
        assert type(k[0]) is str, "Type name should be str"
        assert type(k[1]) is str, "Op name should be str"
    else:
        assert type(k) is str, "Sole op name should be str"
