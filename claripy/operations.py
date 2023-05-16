from __future__ import annotations
from typing import TYPE_CHECKING, Any, Callable, Dict, Optional, Tuple, Type, TypeVar, Union, List
import itertools

from . import fp
from . import ast
from . import simplifications
from .errors import ClaripyOperationError, ClaripyTypeError
from . import debug as _d

TArgType = TypeVar("TArgType", bound=Any)  # basic type for argument
TReturnType = TypeVar("TReturnType", bound=Any)


def op(
    name: str,
    arg_types: tuple[type[TArgType], ...] | type[TArgType],
    return_type: type[TReturnType],
    extra_check: Callable | None = None,
    calc_length=None,
    do_coerce=True,
    bound=True,
) -> Callable[..., TReturnType]:  # pylint:disable=unused-argument
    """_summary_

    Args:
        name (str): operation name, passed to SimplificationManager
        arg_types (tuple[Type[TArgType], ...] | Type[TArgType]): function's input TYPE or inputs' TYPE
        return_type (Type[TReturnType]): return type, the final value will be converted to this type
        extra_check (Callable | None, optional): extra checking function. Defaults to None.
        calc_length (_type_, optional): TODO. Defaults to None.
        do_coerce (bool, optional): TODO. Defaults to True.
        bound (bool, optional): TODO. Defaults to True.

    Raises:
        ClaripyOperationError: _description_
        ClaripyTypeError: _description_
        ClaripyOperationError: _description_

    Returns:
        Callable[..., TReturnType]: _description_

    Yields:
        Iterator[Callable[..., TReturnType]]: _description_
    """
    if type(arg_types) in (tuple, list):  # pylint:disable=unidiomatic-typecheck
        expected_num_args = len(arg_types)
    elif type(arg_types) is type:  # pylint:disable=unidiomatic-typecheck
        expected_num_args = None
    else:
        raise ClaripyOperationError(f"op {name} got weird arg_types")

    def _type_fixer(args):
        num_args = len(args)
        if expected_num_args is not None and num_args != expected_num_args:
            if num_args + 1 == expected_num_args and arg_types[0] is fp.RM:
                args = (fp.RM.default(),) + args
            else:
                raise ClaripyTypeError(
                    "Operation {} takes exactly " "{} arguments ({} given)".format(name, len(arg_types), len(args))
                )

        if type(arg_types) is type:  # pylint:disable=unidiomatic-typecheck
            actual_arg_types = (arg_types,) * num_args
        else:
            actual_arg_types = arg_types
        matches = [isinstance(arg, argty) for arg, argty in zip(args, actual_arg_types)]

        # heuristically, this works!
        thing = args[matches.index(True, 1 if actual_arg_types[0] is fp.RM else 0)] if True in matches else None

        for arg, argty, matches in zip(args, actual_arg_types, matches):
            if not matches:
                if do_coerce and hasattr(argty, "_from_" + type(arg).__name__):
                    convert = getattr(argty, "_from_" + type(arg).__name__)
                    yield convert(thing, arg)
                else:
                    yield NotImplemented
                    return
            else:
                yield arg

    def _op(*args):
        fixed_args = tuple(_type_fixer(args))
        if _d._DEBUG:
            for i in fixed_args:
                if i is NotImplemented:
                    return NotImplemented
            if extra_check is not None:
                success, msg = extra_check(*fixed_args)
                if not success:
                    raise ClaripyOperationError(msg)

        # pylint:disable=too-many-nested-blocks
        simp = _handle_annotations(simplifications.simpleton.simplify(name, fixed_args), args)
        if simp is not None:
            return simp

        kwargs = {}
        if calc_length is not None:
            kwargs["length"] = calc_length(*fixed_args)

        kwargs["uninitialized"] = None
        # pylint:disable=isinstance-second-argument-not-valid-type
        if any(a.uninitialized is True for a in args if isinstance(a, ast.Base)):
            kwargs["uninitialized"] = True
        if name in preprocessors:
            args, kwargs = preprocessors[name](*args, **kwargs)

        return return_type(name, fixed_args, **kwargs)

    _op.calc_length = calc_length
    return _op


def _handle_annotations(simp: String | BV | Bool | FP | None, args: Any) -> String | BV | Bool | FP | None:
    if simp is None:
        return None

    # pylint:disable=isinstance-second-argument-not-valid-type
    ast_args = tuple(a for a in args if isinstance(a, ast.Base))
    preserved_relocatable = frozenset(simp._relocatable_annotations)
    relocated_annotations = set()
    bad_eliminated = 0

    for aa in ast_args:
        for oa in aa._relocatable_annotations:
            if oa not in preserved_relocatable and oa not in relocated_annotations:
                relocated_annotations.add(oa)
                na = oa.relocate(aa, simp)
                if na is not None:
                    simp = simp.append_annotation(na)

        bad_eliminated += len(aa._uneliminatable_annotations - simp._uneliminatable_annotations)

    if bad_eliminated == 0:
        return simp
    return None


TOpFunc = Callable[..., TReturnType]


def reversed_op(op_func: TOpFunc) -> TOpFunc:
    if type(op_func) is not type(reversed_op):
        op_func = op_func.im_func  # unwrap instancemethod into function

    def _reversed_op(*args):
        return op_func(*args[::-1])

    return _reversed_op


#
# Extra processors
#

union_counter = itertools.count()


def preprocess_union(*args, **kwargs) -> tuple[tuple[BV, BV], dict[str, int | frozenset | None]]:
    #
    # When we union two values, we implicitly create a new symbolic, multi-valued
    # variable, because a union is essentially an ITE with an unconstrained
    # "choice" variable.
    #

    new_name = "union_%d" % next(union_counter)
    kwargs["add_variables"] = frozenset((new_name,))
    return args, kwargs


preprocessors = {
    "union": preprocess_union,
    # 'intersection': preprocess_intersect
}

#
# Length checkers
#


def length_same_check(*args) -> tuple[bool, str]:
    return all(a.length == args[0].length for a in args), "args' length must all be equal"


def basic_length_calc(*args) -> int:
    return args[0].length


def extract_check(high: int, low: int, bv: BV) -> tuple[bool, str]:
    if high < 0 or low < 0:
        return False, "Extract high and low must be nonnegative"
    elif low > high:
        return False, "Extract low must be <= high"
    elif high >= bv.size():
        return False, "Extract bound must be less than BV size"

    return True, ""


def extend_check(amount: int, value: BV) -> tuple[bool, str]:  # pylint: disable=unused-argument
    return amount >= 0, "Extension length must be nonnegative"


def concat_length_calc(*args) -> int:
    return sum(arg.length for arg in args)


def extract_length_calc(high: int, low: int, _: BV) -> int:
    return high + 1 - low


def str_basic_length_calc(str_1):
    return str_1.length


def int_to_str_length_calc(int_val: BV) -> int:  # pylint: disable=unused-argument
    return 8 * ast.String.MAX_LENGTH


def str_replace_check(*args) -> tuple[bool, str]:
    str_1, str_2, _ = args
    if str_1.length < str_2.length:
        return False, "The pattern that has to be replaced is longer than the string itself"
    return True, ""


def substr_length_calc(start_idx: BV, count: BV, strval: String) -> int:  # pylint: disable=unused-argument
    # FIXME: How can I get the value of a concrete object without a solver
    return strval.length if not count.concrete else 8 * count.args[0]


def ext_length_calc(ext: int, orig: BV) -> int:
    return orig.length + ext


def str_concat_length_calc(*args) -> int:
    return sum(arg.length for arg in args)


def str_replace_length_calc(*args) -> int:
    str_1, str_2, str_3 = args
    # Return the maximum length that the string can assume after the replace
    # operation
    #
    # If the part that has to be replaced if greater than
    # the replacement than the we have the maximum length possible
    # when the part that has to be replaced is not found inside the string
    if str_2.length >= str_3.length:
        return str_1.length
    # Otherwise We have the maximum length when teh replacement happens
    return str_1.length - str_2.length + str_3.length


def strlen_bv_size_calc(s: String, bitlength: int) -> int:  # pylint: disable=unused-argument
    return bitlength


def strindexof_bv_size_calc(
    s1: String, s2: String, start_idx: BV, bitlength: int
) -> int:  # pylint: disable=unused-argument
    return bitlength


def strtoint_bv_size_calc(s: String, bitlength: int) -> int:  # pylint: disable=unused-argument
    return bitlength


#
# Operation lists
#

expression_arithmetic_operations = {
    # arithmetic
    "__add__",
    "__radd__",
    "__truediv__",
    "__rtruediv__",
    "__floordiv__",
    "__rfloordiv__",
    "__mul__",
    "__rmul__",
    "__sub__",
    "__rsub__",
    "__pow__",
    "__rpow__",
    "__mod__",
    "__rmod__",
    "SDiv",
    "SMod",
    "__neg__",
    "__abs__",
}

bin_ops = {
    "__add__",
    "__radd__",
    "__mul__",
    "__rmul__",
    "__or__",
    "__ror__",
    "__and__",
    "__rand__",
    "__xor__",
    "__rxor__",
}

expression_comparator_operations = {
    # comparisons
    "__eq__",
    "__ne__",
    "__ge__",
    "__le__",
    "__gt__",
    "__lt__",
}

# expression_comparator_operations = {
#     'Eq',
#     'Ne',
#     'Ge', 'Le',
#     'Gt', 'Lt',
# }

expression_bitwise_operations = {
    # bitwise
    "__invert__",
    "__or__",
    "__ror__",
    "__and__",
    "__rand__",
    "__xor__",
    "__rxor__",
    "__lshift__",
    "__rlshift__",
    "__rshift__",
    "__rrshift__",
}

expression_set_operations = {
    # Set operations
    "union",
    "intersection",
    "widen",
}

expression_operations = (
    expression_arithmetic_operations
    | expression_comparator_operations
    | expression_bitwise_operations
    | expression_set_operations
)

backend_comparator_operations = {
    "SGE",
    "SLE",
    "SGT",
    "SLT",
    "UGE",
    "ULE",
    "UGT",
    "ULT",
}

backend_bitwise_operations = {
    "RotateLeft",
    "RotateRight",
    "LShR",
    "Reverse",
}

backend_boolean_operations = {"And", "Or", "Not"}

backend_bitmod_operations = {"Concat", "Extract", "SignExt", "ZeroExt"}

backend_creation_operations = {"BoolV", "BVV", "FPV", "StringV"}

backend_symbol_creation_operations = {"BoolS", "BVS", "FPS", "StringS"}

backend_other_operations = {"If"}

backend_arithmetic_operations = {"SDiv", "SMod"}

backend_operations = (
    backend_comparator_operations
    | backend_bitwise_operations
    | backend_boolean_operations
    | backend_bitmod_operations
    | backend_creation_operations
    | backend_other_operations
    | backend_arithmetic_operations
)
backend_operations_vsa_compliant = (
    backend_bitwise_operations | backend_comparator_operations | backend_boolean_operations | backend_bitmod_operations
)
backend_operations_all = backend_operations | backend_operations_vsa_compliant

backend_fp_cmp_operations = {
    "fpLT",
    "fpLEQ",
    "fpGT",
    "fpGEQ",
    "fpEQ",
}

backend_fp_operations = {
    "FPS",
    "fpToFP",
    "fpToFPUnsigned",
    "fpToIEEEBV",
    "fpFP",
    "fpToSBV",
    "fpToUBV",
    "fpNeg",
    "fpSub",
    "fpAdd",
    "fpMul",
    "fpDiv",
    "fpAbs",
    "fpIsNaN",
    "fpIsInf",
    "fpSqrt",
} | backend_fp_cmp_operations

backend_strings_operations = {
    "StrSubstr",
    "StrReplace",
    "StrConcat",
    "StrLen",
    "StrContains",
    "StrPrefixOf",
    "StrSuffixOf",
    "StrIndexOf",
    "StrToInt",
    "StrIsDigit",
    "IntToStr",
}

opposites = {
    "__add__": "__radd__",
    "__radd__": "__add__",
    "__truediv__": "__rtruediv__",
    "__rtruediv__": "__truediv__",
    "__floordiv__": "__rfloordiv__",
    "__rfloordiv__": "__floordiv__",
    "__mul__": "__rmul__",
    "__rmul__": "__mul__",
    "__sub__": "__rsub__",
    "__rsub__": "__sub__",
    "__pow__": "__rpow__",
    "__rpow__": "__pow__",
    "__mod__": "__rmod__",
    "__rmod__": "__mod__",
    "__eq__": "__eq__",
    "__ne__": "__ne__",
    "__ge__": "__le__",
    "__le__": "__ge__",
    "__gt__": "__lt__",
    "__lt__": "__gt__",
    "ULT": "UGT",
    "UGT": "ULT",
    "ULE": "UGE",
    "UGE": "ULE",
    "SLT": "SGT",
    "SGT": "SLT",
    "SLE": "SGE",
    "SGE": "SLE",
    # '__neg__':
    # '__abs__':
    # '__invert__':
    "__or__": "__ror__",
    "__ror__": "__or__",
    "__and__": "__rand__",
    "__rand__": "__and__",
    "__xor__": "__rxor__",
    "__rxor__": "__xor__",
    "__lshift__": "__rlshift__",
    "__rlshift__": "__lshift__",
    "__rshift__": "__rrshift__",
    "__rrshift__": "__rshift__",
}

reversed_ops = {
    "__radd__": "__add__",
    "__rand__": "__and__",
    "__rfloordiv__": "__floordiv__",
    "__rlshift__": "__lshift__",
    "__rmod__": "__mod__",
    "__rmul__": "__mul__",
    "__ror__": "__or__",
    "__rpow__": "__pow__",
    "__rrshift__": "__rshift__",
    "__rsub__": "__sub__",
    "__rtruediv__": "__truediv__",
    "__rxor__": "__xor__",
}

inverse_operations = {
    "__eq__": "__ne__",
    "__ne__": "__eq__",
    "__gt__": "__le__",
    "__lt__": "__ge__",
    "__ge__": "__lt__",
    "__le__": "__gt__",
    "ULT": "UGE",
    "UGE": "ULT",
    "UGT": "ULE",
    "ULE": "UGT",
    "SLT": "SGE",
    "SGE": "SLT",
    "SLE": "SGT",
    "SGT": "SLE",
}

leaf_operations = backend_symbol_creation_operations | backend_creation_operations
leaf_operations_concrete = backend_creation_operations
leaf_operations_symbolic = backend_symbol_creation_operations
leaf_operations_symbolic_with_union = leaf_operations_symbolic | {"union"}

#
# Reversibility
#

not_invertible = {"union"}
reverse_distributable = {
    "widen",
    "union",
    "intersection",
    "__invert__",
    "__or__",
    "__ror__",
    "__and__",
    "__rand__",
    "__xor__",
    "__rxor__",
}

infix = {
    "__add__": "+",
    "__sub__": "-",
    "__mul__": "*",
    "__floordiv__": "/",
    "__truediv__": "/",  # the raw / operator should use integral semantics on bitvectors
    "__pow__": "**",
    "__mod__": "%",
    "__eq__": "==",
    "__ne__": "!=",
    "__ge__": ">=",
    "__le__": "<=",
    "__gt__": ">",
    "__lt__": "<",
    "UGE": ">=",
    "ULE": "<=",
    "UGT": ">",
    "ULT": "<",
    "SGE": ">=s",
    "SLE": "<=s",
    "SGT": ">s",
    "SLT": "<s",
    "SDiv": "/s",
    "SMod": "%s",
    "__or__": "|",
    "__and__": "&",
    "__xor__": "^",
    "__lshift__": "<<",
    "__rshift__": ">>",
    "And": "&&",
    "Or": "||",
    "Concat": "..",
}

prefix = {
    "Not": "!",
    "__neg__": "-",
    "__invert__": "~",
}

op_precedence = {  # based on https://en.cppreference.com/w/c/language/operator_precedence
    # precedence: 2
    "__pow__": 2,
    "Not": 2,
    "__neg__": 2,
    "__invert__": 2,
    # precedence: 3
    "__mul__": 3,
    "__floordiv__": 3,
    "__truediv__": 3,  # the raw / operator should use integral semantics on bitvectors
    "__mod__": 3,
    "SDiv": 3,
    "SMod": 3,
    # precedence: 4
    "__add__": 4,
    "__sub__": 4,
    # precedence: 5
    "__lshift__": 5,
    "__rshift__": 5,
    # precedence: 6
    "__ge__": 6,
    "__le__": 6,
    "__gt__": 6,
    "__lt__": 6,
    "UGE": 6,
    "ULE": 6,
    "UGT": 6,
    "ULT": 6,
    "SGE": 6,
    "SLE": 6,
    "SGT": 6,
    "SLT": 6,
    # precedence: 7
    "__eq__": 7,
    "__ne__": 7,
    # precedence: 8
    "__and__": 8,
    # precedence: 9
    "__xor__": 9,
    # precedence: 10
    "__or__": 10,
    # precedence: 11
    "And": 11,
    # precedence: 12
    "Or": 12,
    # 'Concat': '..',
}

commutative_operations = {
    "__and__",
    "__or__",
    "__xor__",
    "__add__",
    "__mul__",
    "And",
    "Or",
    "Xor",
}

if TYPE_CHECKING:  # pylint: disable=duplicate-code
    from claripy.ast.bool import Bool
    from claripy.ast.bv import BV
    from claripy.ast.fp import FP
    from claripy.ast.strings import String
