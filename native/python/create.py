__all__ = ["bool_s", "bv_s", "fp_s", "bv_v", "bool_v", "fp_v", "if_"]

from claricpp import *
from expr import *
from annotation_spav import AnnotationSPAV
from functools import cache, cached_property

# TODO: deal with destruction / freeing memory
# TODO: slots!


empty = AnnotationSPAV()

######################################################################
#                              Symbols                               #
######################################################################

def bool_s(name: bytes, spav: AnnotationSPAV = None) -> Expr:
    '''
    :param name: The name of the expr
    :param spav: The annotations to be held by the expr
    :return: A symbolic Bool expr
    '''
    raw = (empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_symbol_bool(name, raw))

def string_s(name: bytes, bit_length: int, spav: AnnotationSPAV = None) -> Expr:
    '''
    :param name: The name of the expr
    :param bit_length: The bit_length of the expr
    :param spav: The annotations to be held by the expr
    :return: A symbolic String expr
    '''
    raw = (empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_symbol_string(name, bit_length, raw))

def bv_s(name: bytes, bit_length: int, spav: AnnotationSPAV = None) -> Expr:
    '''
    :param name: The name of the expr
    :param bit_length: The bit_length of the expr
    :param spav: The annotations to be held by the expr
    :return: A symbolic BV expr
    '''
    raw = (empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_symbol_bv(name, bit_length, raw))

def fp_s(name: bytes, bit_length: int, spav: AnnotationSPAV = None) -> Expr:
    '''
    :param name: The name of the expr
    :param bit_length: The bit_length of the expr
    :param spav: The annotations to be held by the expr
    :return: A symbolic FP expr
    '''
    raw = (empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_symbol_fp(name, bit_length, raw))

def vs_s(name: bytes, bit_length: int, spav: AnnotationSPAV = None) -> Expr:
    '''
    :param name: The name of the expr
    :param bit_length: The bit_length of the expr
    :param spav: The annotations to be held by the expr
    :return: A symbolic VS expr
    '''
    raw = (empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_symbol_fp(name, bit_length, raw))

######################################################################
#                              Literals                              #
######################################################################

def bool_v(value: bool, spav: AnnotationSPAV = None) -> Expr:
    '''
    :param value: The name of the expr
    :param spav: The annotations to be held by the expr
    :return: A Bool expr with the given value
    '''
    raw = (empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_literal_bool(value, raw))


def string_v(value: bytes, spav: AnnotationSPAV = None) -> Expr:
    '''
    :param value: The value of expr
    :param spav: The annotations to be held by the expr
    :return: A String expr with the given value
    '''
    raw = (empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_literal_string(value, raw))


def bv_v(value: Union[int, bytes], bit_length: int, spav: AnnotationSPAV = None) -> Expr:
    '''
    :param value: The name of the expr, can be an int or in decimal representation in bytes (e.x. b"1.23")
    :param bit_length: The bit length of the BV
    :param spav: The annotations to be held by the expr
    :return: A BV expr with the given value
    '''
    raw = (empty if spav is None else spav).raw
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


def fp_v(value: float, double: bool = true, spav: AnnotationSPAV = None) -> Expr:
    '''
    :param value: The name of the expr
    :param double: True if the fp should be a 64-bit float, false implies 32-bit
    :param spav: The annotations to be held by the expr
    :return: A FP expr with the given value
    '''
    raw = (empty if spav is None else spav).raw
    if double:
        return Expr(claricpp.claricpp_create_literal_fp_double(value, raw))
    return Expr(claricpp.claricpp_create_literal_fp_float(value, raw))

def vs_v(hash: int, value: int, bit_length: int, spav: AnnotationSPAV = None) -> Expr:
    '''
    :param hash: The hash of the VS object
    :param value: A value or reference to the VS object
    :param bit_length: The bit length of the VS object
    :param spav: The annotations to be held by the expr
    :return: A VS expr with the given value
    '''
    raw = (empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_literal_vs(hash, value, bit_length, raw))


######################################################################
#                       Claricpp 'Non-trivial'                       #
######################################################################


def if_(cond: Expr, left: Expr, right: Expr, spav: AnnotationSPAV = None) -> Expr:
    '''
    :param cond: The condition
    :param left: The if true statement
    :param right: The if false statement
    :param spav: The annotations to be held by the expr
    :return: An if_ expr with the given arguments
    '''
    raw = (empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_if(cond.raw, left.raw, right.raw, raw))

def extract(high: int, low: int, from_: Expr, spav: AnnotationSPAV) -> Expr:
    '''
    :param high:  The high index for the Extract op
    :param low: The low index for the Extract op
    :param from_: The Expr to extract from
    :param spav: The annotations to be held by the expr
    :return: An extract expr with the given arguments
    '''
    raw = (empty if spav is None else spav).raw
    return Expr(claricpp.claricpp_create_if(high, low, from.raw, raw))


######################################################################
#                         Claricpp 'Trivial'                         #
######################################################################


