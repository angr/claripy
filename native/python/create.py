__all__ = [
    "bool_s",
    "string_s",
    "bv_s",
    "fp_s",
    "vs_s",
    "bv_v",
    "bool_v",
    "fp_v",
    "string_v",
    "vs_v",
    "if_",
    "extract",
    "abs_",
    "neg",
    "not_",
    "invert",
    "reverse",
    "sign_ext",
    "zero_ext",
    "eq",
    "neq",
    "slt",
    "sle",
    "sgt",
    "sge",
    "ult",
    "ule",
    "ugt",
    "uge",
    "sub",
    "sdiv",
    "udiv",
    "smod",
    "umod",
    "shl",
    "shlr",
    "shar",
    "widen",
    "union",
    "intersection",
    "concat",
    "add",
    "mul",
    "or_",
    "and_",
    "xor",
    "to_ieee_bv",
    "ClaricppRM",
    "fp_add",
    "fp_sub",
    "fp_mul",
    "fp_div",
    "fp",
]

from claricpp import *
from expr import *
from annotation_spav import AnnotationSPAV
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


def bool_s(name: bytes, spav: AnnotationSPAV = None) -> Expr:
    """
    :param name: The name of the expr
    :param spav: The annotations to be held by the expr
    :return: A symbolic Bool expr
    """
    raw = (_empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_symbol_bool(name, raw))


def string_s(name: bytes, bit_length: int, spav: AnnotationSPAV = None) -> Expr:
    """
    :param name: The name of the expr
    :param bit_length: The bit_length of the expr
    :param spav: The annotations to be held by the expr
    :return: A symbolic String expr
    """
    raw = (_empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_symbol_string(name, bit_length, raw))


def bv_s(name: bytes, bit_length: int, spav: AnnotationSPAV = None) -> Expr:
    """
    :param name: The name of the expr
    :param bit_length: The bit_length of the expr
    :param spav: The annotations to be held by the expr
    :return: A symbolic BV expr
    """
    raw = (_empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_symbol_bv(name, bit_length, raw))


def fp_s(name: bytes, bit_length: int, spav: AnnotationSPAV = None) -> Expr:
    """
    :param name: The name of the expr
    :param bit_length: The bit_length of the expr
    :param spav: The annotations to be held by the expr
    :return: A symbolic FP expr
    """
    raw = (_empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_symbol_fp(name, bit_length, raw))


def vs_s(name: bytes, bit_length: int, spav: AnnotationSPAV = None) -> Expr:
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


def bool_v(value: bool, spav: AnnotationSPAV = None) -> Expr:
    """
    :param value: The name of the expr
    :param spav: The annotations to be held by the expr
    :return: A Bool expr with the given value
    """
    raw = (_empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_literal_bool(value, raw))


def string_v(value: bytes, spav: AnnotationSPAV = None) -> Expr:
    """
    :param value: The value of expr
    :param spav: The annotations to be held by the expr
    :return: A String expr with the given value
    """
    raw = (_empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_literal_string(value, raw))


def bv_v(
    value: Union[int, bytes], bit_length: int, spav: AnnotationSPAV = None
) -> Expr:
    """
    :param value: The name of the expr, can be an int or in decimal representation in bytes (e.x. b"1.23")
    :param bit_length: The bit length of the BV
    :param spav: The annotations to be held by the expr
    :return: A BV expr with the given value
    """
    raw = (_empty if spav is None else spav).raw
    if type(value) == bytes:
        expr = claricpp.claricpp_create_literal_bv_big_int_mode_str(
            value, bit_length, raw
        )
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


def fp_v(value: float, double: bool = True, spav: AnnotationSPAV = None) -> Expr:
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


def vs_v(hash: int, value: int, bit_length: int, spav: AnnotationSPAV = None) -> Expr:
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


def if_(cond: Expr, left: Expr, right: Expr, spav: AnnotationSPAV = None) -> Expr:
    """
    :param cond: The condition
    :param left: The if true statement
    :param right: The if false statement
    :param spav: The annotations to be held by the expr
    :return: An if_ expr with the given arguments
    """
    raw = (_empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_if(cond.raw, left.raw, right.raw, raw))


def extract(high: int, low: int, from_: Expr, spav: AnnotationSPAV = None) -> Expr:
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


abs_ = _unary(claricpp.claricpp_create_abs)
neg = _unary(claricpp.claricpp_create_neg)
not_ = _unary(claricpp.claricpp_create_not)
invert = _unary(claricpp.claricpp_create_invert)
reverse = _unary(claricpp.claricpp_create_reverse)

sign_ext = _uint_binary(claricpp.claricpp_create_sign_ext)
zero_ext = _uint_binary(claricpp.claricpp_create_zero_ext)

eq = _binary(claricpp.claricpp_create_eq)
neq = _binary(claricpp.claricpp_create_neq)

slt = _binary(claricpp.claricpp_create_slt)
sle = _binary(claricpp.claricpp_create_sle)
sgt = _binary(claricpp.claricpp_create_sgt)
sge = _binary(claricpp.claricpp_create_sge)
ult = _binary(claricpp.claricpp_create_ult)
ule = _binary(claricpp.claricpp_create_ule)
ugt = _binary(claricpp.claricpp_create_ugt)
uge = _binary(claricpp.claricpp_create_uge)

sub = _binary(claricpp.claricpp_create_sub)
sdiv = _binary(claricpp.claricpp_create_sdiv)
udiv = _binary(claricpp.claricpp_create_udiv)
smod = _binary(claricpp.claricpp_create_smod)
umod = _binary(claricpp.claricpp_create_umod)

shl = _binary(claricpp.claricpp_create_shift_left)
shlr = _binary(claricpp.claricpp_create_shift_logical_right)
shar = _binary(claricpp.claricpp_create_shift_arithmetic_right)

widen = _binary(claricpp.claricpp_create_widen)
union = _binary(claricpp.claricpp_create_union)
intersection = _binary(claricpp.claricpp_create_intersection)
concat = _binary(claricpp.claricpp_create_concat)

add = _flat(claricpp.claricpp_create_add)
mul = _flat(claricpp.claricpp_create_mul)

or_ = _flat(claricpp.claricpp_create_or)
and_ = _flat(claricpp.claricpp_create_and)
xor = _flat(claricpp.claricpp_create_xor)


######################################################################
#                           Claricpp String                          #
######################################################################


def int2str(x: Expr, spav: AnnotationSPAV = None) -> Expr:
    raw = (_empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_string_from_int(x.raw, raw))


def index_of(
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


def replace(
    full: Expr, search: Expr, replacement: Expr, spav: AnnotationSPAV = None
) -> Expr:
    raw = (_empty if spav is None else spav).raw
    return Expr(
        claricpp.claricpp_create_string_index_of(
            full.raw, search.raw, replacement.raw, raw
        )
    )


def substr(
    start_index: Expr, count: Expr, full_string: Expr, spav: AnnotationSPAV = None
) -> Expr:
    raw = (_empty if spav is None else spav).raw
    return Expr(
        claricpp.claricpp_create_string_index_of(
            start_index.raw, count.raw, full_string.raw, raw
        )
    )


is_digit = _unary(claricpp.claricpp_create_string_is_digit)
to_int = _uint_binary(claricpp.claricpp_create_string_to_int)
strlen = _uint_binary(claricpp.claricpp_create_string_len)
contains = _binary(claricpp.claricpp_create_string_contains)
prefix_of = _binary(claricpp.claricpp_create_string_prefix_of)
suffix_of = _binary(claricpp.claricpp_create_string_suffix_of)


######################################################################
#                             Claricpp FP                            #
######################################################################

# todo: ClaricppExpr claricpp_create_fp_from_2s_complement_bv_signed(const ClaricppRM mode, const ClaricppExpr x, const uint32_t exp_width, const uint32_t mantissa_width, ClaricppSPAV spav);
# todo: ClaricppExpr claricpp_create_fp_from_2s_complement_bv_unsigned(const ClaricppRM mode, const ClaricppExpr x, const uint32_t exp_width, const uint32_t mantissa_width, ClaricppSPAV spav);
# todo: ClaricppExpr claricpp_create_fp_from_fp(const ClaricppRM mode, const ClaricppExpr fp, const uint32_t exp_width, const uint32_t mantissa_width, ClaricppSPAV spav);
# todo: ClaricppExpr claricpp_create_fp_from_not_2s_complement_bv(const ClaricppExpr x, const uint32_t exp_width, const uint32_t mantissa_width, ClaricppSPAV spav);
# todo: ClaricppExpr claricpp_create_fp_to_bv_signed(const ClaricppRM mode, const ClaricppExpr fp, const UINT bit_length, ClaricppSPAV spav);
# todo: ClaricppExpr claricpp_create_fp_to_bv_unsigned(const ClaricppRM mode, const ClaricppExpr fp, const UINT bit_length, ClaricppSPAV spav);

to_ieee_bv = _unary(claricpp.claricpp_create_fp_to_ieee_bv)

fp_add = _mode_binary(claricpp.claricpp_create_fp_add)
fp_sub = _mode_binary(claricpp.claricpp_create_fp_sub)
fp_mul = _mode_binary(claricpp.claricpp_create_fp_mul)
fp_div = _mode_binary(claricpp.claricpp_create_fp_div)

fp = _ternary(claricpp.claricpp_create_fp_fp)
