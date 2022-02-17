__all__ = [
    "create",
    "ClaricppRM",
    "BoolS",
    "StringS",
    "BVS",
    "FPS",
    "VSS",
    "BoolV",
    "StringV",
    "BVV",
    "FPV",
    "VSV",
    "If",
    "Extract",
    "f__abs__",
    "f__neg__",
    "Not",
    "f__invert__",
    "Reverse",
    "SignExt",
    "ZeroExt",
    "f__eq__",
    "f__neq__",
    "SLT",
    "SLE",
    "SGT",
    "SGE",
    "ULT",
    "ULE",
    "UGT",
    "UGE",
    "f__lt__",
    "f__le__",
    "f__gt__",
    "f__ge__",
    "f__sub__",
    "SDiv",
    "f__floordiv__",
    "SMod",
    "f__mod__",
    "f__lshift__",
    "LShR",
    "f__rshift__",
    "widen",
    "union",
    "intersection",
    "Concat",
    "f__add__",
    "f__mul__",
    "f__or__",
    "f__and__",
    "f__xor__",
    "IntToStr",
    "StrIndexOf",
    "StrReplace",
    "StrSubStr",
    "StrIsDigit",
    "StrToInt",
    "StrLen",
    "StrContains",
    "StrPrefixOf",
    "StrSuffixOf",
    "fpToIEEEBV",
    "fpAdd",
    "fpSub",
    "fpMul",
    "fpDiv",
    "fpFP",
]


# TODO: deprecate old operators
# TODO: reverse ops: __radd__ etc

from .claricpp import *
from .expr import *
from .op_names import *
from .annotation_spav import AnnotationSPAV
from typing import List, Union
from enum import Enum

# TODO: deal with destruction / freeing memory
# TODO: slots!

# An empty SPAV (used as a default spav)
_empty = AnnotationSPAV()


class ClaricppRM(Enum):
    """
    Wraps a claricpp rounding mode
    """

    NearestTiesEven = (claricpp.ClaricppRmNearestTiesEven,)
    NearestTiesAwayFromZero = (claricpp.ClaricppRmNearestTiesAwayFromZero,)
    TowardsZero = (claricpp.ClaricppRmTowardsZero,)
    TowardsPositiveInf = (claricpp.ClaricppRmTowardsPositiveInf,)
    TowardsNegativeInf = claricpp.ClaricppRmTowardsNegativeInf


######################################################################
#                              Symbols                               #
######################################################################


def BoolS(name: bytes, spav: AnnotationSPAV = None) -> Expr:
    """
    :param name: The name of the expr
    :param spav: The annotations to be held by the expr
    :return: A symbolic Bool expr
    """
    raw = (_empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_symbol_bool(name, raw))


def StringS(name: bytes, bit_length: int, spav: AnnotationSPAV = None) -> Expr:
    """
    :param name: The name of the expr
    :param bit_length: The bit_length of the expr
    :param spav: The annotations to be held by the expr
    :return: A symbolic String expr
    """
    raw = (_empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_symbol_string(name, bit_length, raw))


def BVS(name: bytes, bit_length: int, spav: AnnotationSPAV = None) -> Expr:
    """
    :param name: The name of the expr
    :param bit_length: The bit_length of the expr
    :param spav: The annotations to be held by the expr
    :return: A symbolic BV expr
    """
    raw = (_empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_symbol_bv(name, bit_length, raw))


def FPS(name: bytes, bit_length: int, spav: AnnotationSPAV = None) -> Expr:
    """
    :param name: The name of the expr
    :param bit_length: The bit_length of the expr
    :param spav: The annotations to be held by the expr
    :return: A symbolic FP expr
    """
    raw = (_empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_symbol_fp(name, bit_length, raw))


def VSS(name: bytes, bit_length: int, spav: AnnotationSPAV = None) -> Expr:
    """
    :param name: The name of the expr
    :param bit_length: The bit_length of the expr
    :param spav: The annotations to be held by the expr
    :return: A symbolic VS expr
    """
    raw = (_empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_symbol_fp(name, bit_length, raw))


######################################################################
#                              Literals                              #
######################################################################


def BoolV(value: bool, spav: AnnotationSPAV = None) -> Expr:
    """
    :param value: The name of the expr
    :param spav: The annotations to be held by the expr
    :return: A Bool expr with the given value
    """
    raw = (_empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_literal_bool(value, raw))


def StringV(value: bytes, spav: AnnotationSPAV = None) -> Expr:
    """
    :param value: The value of expr
    :param spav: The annotations to be held by the expr
    :return: A String expr with the given value
    """
    raw = (_empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_literal_string(value, raw))


def BVV(value: Union[int, bytes], bit_length: int, spav: AnnotationSPAV = None) -> Expr:
    """
    :param value: The name of the expr, can be an int or in decimal representation in bytes (e.x. b"1.23")
    :param bit_length: The bit length of the BV
    :param spav: The annotations to be held by the expr
    :return: A BV expr with the given value
    """
    raw = (_empty if spav is None else spav).raw
    if type(value) == bytes:
        # We prefer the default mode rather than forcing one
        expr = claricpp.claricpp_create_literal_bv_big_int(value, bit_length, raw)
    elif bit_length == 8:
        expr = claricpp.claricpp_create_literal_bv_u8(value, raw)
    elif bit_length == 16:
        expr = claricpp.claricpp_create_literal_bv_u16(value, raw)
    elif bit_length == 32:
        expr = claricpp.claricpp_create_literal_bv_u32(value, raw)
    elif bit_length == 64:
        expr = claricpp.claricpp_create_literal_bv_u64(value, raw)
    else:
        data = str(value).encode()
        expr = claricpp.claricpp_create_literal_bv_big_int_mode_int(
            str(value).encode(), bit_length, raw
        )
    return Expr(expr)


def FPV(value: float, double: bool = True, spav: AnnotationSPAV = None) -> Expr:
    """
    :param value: The name of the expr
    :param double: True if the fp should be a 64-bit float, false implies 32-bit
    :param spav: The annotations to be held by the expr
    :return: A FP expr with the given value
    """
    raw = (_empty if spav is None else spav).raw
    if double:
        return Expr(claricpp.claricpp_create_literal_fp_double(value, raw))
    return Expr(claricpp.claricpp_create_literal_fp_float(value, raw))


def VSV(hash: int, value: int, bit_length: int, spav: AnnotationSPAV = None) -> Expr:
    """
    :param hash: The hash of the VS object
    :param value: A value or reference to the VS object
    :param bit_length: The bit length of the VS object
    :param spav: The annotations to be held by the expr
    :return: A VS expr with the given value
    """
    raw = (_empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_literal_vs(hash, value, bit_length, raw))


######################################################################
#                       Claricpp 'Non-trivial'                       #
######################################################################


def If(cond: Expr, left: Expr, right: Expr, spav: AnnotationSPAV = None) -> Expr:
    """
    :param cond: The condition
    :param left: The if true statement
    :param right: The if false statement
    :param spav: The annotations to be held by the expr
    :return: An if_ expr with the given arguments
    """
    raw = (_empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_if(cond.raw, left.raw, right.raw, raw))


def Extract(high: int, low: int, from_: Expr, spav: AnnotationSPAV = None) -> Expr:
    """
    :param high:  The high index for the Extract op
    :param low: The low index for the Extract op
    :param from_: The Expr to extract from
    :param spav: The annotations to be held by the expr
    :return: An extract expr with the given arguments
    """
    raw = (_empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_if(high, low, from_.raw, raw))


######################################################################
#                     Claricpp Wrapper Functions                     #
######################################################################


def _flat(func):
    def ret(*args: Expr, spav: AnnotationSPAV = None) -> Expr:
        raw = (_empty if spav is None else spav).raw
        exprs = [i.raw for i in args]
        return Expr(func(exprs, len(exprs), raw))

    return ret


def _mode_binary(func):
    def ret(
        left: Expr, right: Expr, mode: ClaricppRM, spav: AnnotationSPAV = None
    ) -> Expr:
        raw = (_empty if spav is None else spav).raw
        return Expr(func(left.raw, right.raw, mode.value, raw))

    return ret


def _unary(func):
    def ret(x: Expr, spav: AnnotationSPAV = None) -> Expr:
        raw = (_empty if spav is None else spav).raw
        return Expr(func(x.raw, raw))

    return ret


def _uint_binary(func):
    def ret(x: Expr, n: int, spav: AnnotationSPAV = None) -> Expr:
        raw = (_empty if spav is None else spav).raw
        return Expr(func(x.raw, n, raw))

    return ret


def _binary(func):
    def ret(left: Expr, right: Expr, spav: AnnotationSPAV = None) -> Expr:
        raw = (_empty if spav is None else spav).raw
        return Expr(func(left.raw, right.raw, raw))

    return ret


def _ternary(func):
    def ret(
        first: Expr, second: Expr, third: Expr, spav: AnnotationSPAV = None
    ) -> Expr:
        raw = (_empty if spav is None else spav).raw
        return Expr(func(first.raw, second.raw, third.raw, raw))

    return ret


######################################################################
#                         Claricpp 'Trivial'                         #
######################################################################


# TODO
f__abs__ = _unary(claricpp.claricpp_create_abs)
f__neg__ = _unary(claricpp.claricpp_create_neg)
Not = _unary(claricpp.claricpp_create_not)
f__invert__ = _unary(claricpp.claricpp_create_invert)
Reverse = _unary(claricpp.claricpp_create_reverse)

SignExt = _uint_binary(claricpp.claricpp_create_sign_ext)
ZeroExt = _uint_binary(claricpp.claricpp_create_zero_ext)

f__eq__ = _binary(claricpp.claricpp_create_eq)
f__neq__ = _binary(claricpp.claricpp_create_neq)

SLT = _binary(claricpp.claricpp_create_slt)
SLE = _binary(claricpp.claricpp_create_sle)
SGT = _binary(claricpp.claricpp_create_sgt)
SGE = _binary(claricpp.claricpp_create_sge)
ULT = _binary(claricpp.claricpp_create_ult)
ULE = _binary(claricpp.claricpp_create_ule)
UGT = _binary(claricpp.claricpp_create_ugt)
UGE = _binary(claricpp.claricpp_create_uge)
f__lt__ = ULT
f__le__ = ULE
f__gt__ = UGT
f__ge__ = UGE

f__sub__ = _binary(claricpp.claricpp_create_sub)
SDiv = _binary(claricpp.claricpp_create_sdiv)
f__floordiv__ = _binary(claricpp.claricpp_create_udiv)
SMod = _binary(claricpp.claricpp_create_smod)
f__mod__ = _binary(claricpp.claricpp_create_umod)

f__lshift__ = _binary(claricpp.claricpp_create_shift_left)
LShR = _binary(claricpp.claricpp_create_shift_logical_right)
f__rshift__ = _binary(claricpp.claricpp_create_shift_arithmetic_right)

widen = _binary(claricpp.claricpp_create_widen)
union = _binary(claricpp.claricpp_create_union)
intersection = _binary(claricpp.claricpp_create_intersection)
Concat = _binary(claricpp.claricpp_create_concat)

f__add__ = _flat(claricpp.claricpp_create_add)
f__mul__ = _flat(claricpp.claricpp_create_mul)

f__or__ = _flat(claricpp.claricpp_create_or)
f__and__ = _flat(claricpp.claricpp_create_and)
f__xor__ = _flat(claricpp.claricpp_create_xor)


######################################################################
#                           Claricpp String                          #
######################################################################


def IntToStr(x: Expr, spav: AnnotationSPAV = None) -> Expr:
    raw = (_empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_string_from_int(x.raw, raw))


def StrIndexOf(
    str_: Expr,
    pattern: Expr,
    start_index: Expr,
    bit_length: int,
    spav: AnnotationSPAV = None,
) -> Expr:
    raw = (_empty if spav is None else spav).raw
    return Expr(
        claricpp.claricpp_create_string_index_of(
            str_.raw, pattern.raw, start_index.raw, bit_length, raw
        )
    )


def StrReplace(
    full: Expr, search: Expr, replacement: Expr, spav: AnnotationSPAV = None
) -> Expr:
    raw = (_empty if spav is None else spav).raw
    return Expr(
        claricpp.claricpp_create_string_index_of(
            full.raw, search.raw, replacement.raw, raw
        )
    )


def StrSubStr(
    start_index: Expr, count: Expr, full_string: Expr, spav: AnnotationSPAV = None
) -> Expr:
    raw = (_empty if spav is None else spav).raw
    return Expr(
        claricpp.claricpp_create_string_index_of(
            start_index.raw, count.raw, full_string.raw, raw
        )
    )


StrIsDigit = _unary(claricpp.claricpp_create_string_is_digit)
StrToInt = _uint_binary(claricpp.claricpp_create_string_to_int)
StrLen = _uint_binary(claricpp.claricpp_create_string_len)
StrContains = _binary(claricpp.claricpp_create_string_contains)
StrPrefixOf = _binary(claricpp.claricpp_create_string_prefix_of)
StrSuffixOf = _binary(claricpp.claricpp_create_string_suffix_of)


######################################################################
#                             Claricpp FP                            #
######################################################################


# todo: ClaricppExpr claricpp_create_fp_from_2s_complement_bv_signed(const ClaricppRM mode, const ClaricppExpr x, const uint32_t exp_width, const uint32_t mantissa_width, ClaricppSPAV spav);
# todo: ClaricppExpr claricpp_create_fp_from_2s_complement_bv_unsigned(const ClaricppRM mode, const ClaricppExpr x, const uint32_t exp_width, const uint32_t mantissa_width, ClaricppSPAV spav);
# todo: ClaricppExpr claricpp_create_fp_from_fp(const ClaricppRM mode, const ClaricppExpr fp, const uint32_t exp_width, const uint32_t mantissa_width, ClaricppSPAV spav);
# todo: ClaricppExpr claricpp_create_fp_from_not_2s_complement_bv(const ClaricppExpr x, const uint32_t exp_width, const uint32_t mantissa_width, ClaricppSPAV spav);
# todo: ClaricppExpr claricpp_create_fp_to_bv_signed(const ClaricppRM mode, const ClaricppExpr fp, const UINT bit_length, ClaricppSPAV spav);
# todo: ClaricppExpr claricpp_create_fp_to_bv_unsigned(const ClaricppRM mode, const ClaricppExpr fp, const UINT bit_length, ClaricppSPAV spav);

fpToIEEEBV = _unary(claricpp.claricpp_create_fp_to_ieee_bv)

fpAdd = _mode_binary(claricpp.claricpp_create_fp_add)
fpSub = _mode_binary(claricpp.claricpp_create_fp_sub)
fpMul = _mode_binary(claricpp.claricpp_create_fp_mul)
fpDiv = _mode_binary(claricpp.claricpp_create_fp_div)

fpFP = _ternary(claricpp.claricpp_create_fp_fp)


######################################################################
#                               Create                               #
######################################################################


op_to_create_func = {
    "BoolS": BoolS,
    "StringS": StringS,
    "BVS": BVS,
    "FPS": FPS,
    "VSS": VSS,
    "BoolV": BoolV,
    "StringV": StringV,
    "BVV": BVV,
    "FPV": FPV,
    "VSV": VSV,
    "If": If,
    "Extract": Extract,
    "__abs__": f__abs__,
    "__neg__": f__neg__,
    "Not": Not,
    "__invert__": f__invert__,
    "Reverse": Reverse,
    "SignExt": SignExt,
    "ZeroExt": ZeroExt,
    "__eq__": f__eq__,
    "__neq__": f__neq__,
    "SLT": SLT,
    "SLE": SLE,
    "SGT": SGT,
    "SGE": SGE,
    "ULT": ULT,
    "ULE": ULE,
    "UGT": UGT,
    "UGE": UGE,
    "__lt__": f__lt__,
    "__le__": f__le__,
    "__gt__": f__gt__,
    "__ge__": f__ge__,
    "__sub__": f__sub__,
    "SDiv": SDiv,
    "__floordiv__": f__floordiv__,
    "SMod": SMod,
    "__mod__": f__mod__,
    "__lshift__": f__lshift__,
    "LShR": LShR,
    "__rshift__": f__rshift__,
    "widen": widen,
    "union": union,
    "intersection": intersection,
    "Concat": Concat,
    "__add__": f__add__,
    "__mul__": f__mul__,
    "__or__": f__or__,
    "__and__": f__and__,
    "__xor__": f__xor__,
    "IntToStr": IntToStr,
    "StrIndexOf": StrIndexOf,
    "StrReplace": StrReplace,
    "StrSubStr": StrSubStr,
    "StrIsDigit": StrIsDigit,
    "StrToInt": StrToInt,
    "StrLen": StrLen,
    "StrContains": StrContains,
    "StrPrefixOf": StrPrefixOf,
    "StrSuffixOf": StrSuffixOf,
    "fpToIEEEBV": fpToIEEEBV,
    "fpAdd": fpAdd,
    "fpSub": fpSub,
    "fpMul": fpMul,
    "fpDiv": fpDiv,
    "fpFP": fpFP,
}


def py_create(op, args, annotations=None):
    """
    Create a new Expr from the python op type op
    """
    if annotations is None:
        spav = None
    else:
        ans = annotations if type(annotations) is list else list(annotations)
        spav = claricpp.claricpp_annotation_create_spav(ans, len(ans))
    return op_to_create_func[op](*args, spav=spav)
