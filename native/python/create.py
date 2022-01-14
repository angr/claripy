__all__ = [ 'bool_s', 'bv_s', 'fp_s', 'bv_v', 'bool_v', 'fp_v', 'if_' ]

from claricpp import *
from expr import *
from annotation_spav import AnnotationSPAV
from functools import cache, cached_property

# TODO: deal with destruction / freeing memory
# TODO: slots!


empty = AnnotationSPAV()


def bool_s(name: bytes, spav = None) -> Expr:
    raw = (empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_symbol_bool(name, raw))

def bv_s(name: bytes, bit_length: int, spav = None) -> Expr:
    raw = (empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_symbol_bv(name, bit_length, raw))

def fp_s(name: bytes, bit_length: int, spav = None) -> Expr:
    raw = (empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_symbol_fp(name, bit_length, raw))

def bool_v(value: bool, spav = None) -> Expr:
    raw = (empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_literal_bool(value, raw))

def bv_v(value: bytes, bit_length: int, spav = None) -> Expr:
    raw = (empty if spav is None else spav).raw
    if type(value) == bytes:
        expr = claricpp.claricpp_create_literal_bv_big_int_mode_str(value, bit_length, raw)
    elif bit_length == 8:
        expr = claricpp.claricpp_create_literal_bv_u8(value, raw)
    elif bit_length == 16:
        expr = claricpp.claricpp_create_literal_bv_u16(value, raw)
    elif bit_length == 32:
        expr = claricpp.claricpp_create_literal_bv_u32(value, raw)
    elif bit_length == 64:
        expr = claricpp.claricpp_create_literal_bv_u64(value, raw)
    else:
        expr = claricpp.claricpp_create_literal_bv_big_int_mode_int(str(value).encode(), bit_length, raw)
    return Expr(expr)

def fp_v(value: float, bit_length: int = 64, spav = None) -> Expr:
    raw = (empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_literal_fp(value, bit_length, raw))

def if_(cond: Expr, left: Expr, right: Expr, spav = None) -> Expr:
    raw = (empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_if(cond.raw, left.raw, right.raw, raw))
