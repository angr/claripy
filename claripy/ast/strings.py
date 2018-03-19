from .bits import Bits
from ..ast.base import _make_name

from .. import operations
from .bool import Bool
from .bv import BV


class String(Bits):
    """
    Base class that represent the AST of a String object and implements all the operation useful to create and modify the AST.

    Do not instantiate this class directly, instead use StringS or StringV to construct a symbol or value, and then use
    operations to construct more complicated expressions.
    """
    def __getitem__(self, rng):
        if type(rng) is slice:
            left = rng.start if rng.start is not None else len(self)-1
            right = rng.stop if rng.stop is not None else 0
            if left < 0:
                left = len(self) + left
            if right < 0:
                right = len(self) + right
            return Substr(left, right, self)
        else:
            return Substr(int(rng), int(rng), self)

def StringS(name, size, uninitialized=False, explicit_name=False, **kwargs):
    """
    Create a new symbolic string (analogous to z3.String())

    :param name:                 The name of the symbolic string (i. e. the name of the variable)
    :param size:                 The size in bytes of the string (i. e. the length of the string)
    :param uninitialized:        Whether this value should be counted as an "uninitialized" value in the course of an
                                 analysis.
    :param bool explicit_name:   If False, an identifier is appended to the name to ensure uniqueness.

    :returns:                    The String object representing the symbolic string
    """
    n = _make_name(name, size, False if explicit_name is None else explicit_name)
    result = String("StringS", (n, uninitialized), length=size, symbolic=True, eager_backends=None, uninitialized=uninitialized, **kwargs)
    return result

def StringV(value, **kwargs):
    """
    Create a new Concrete string (analogous to z3.StringVal())

    :param value: The constant value of the concrete string

    :returns:                    The String object representing the concrete string
    """

    result = String("StringV", (value, len(value)), length=len(value), **kwargs)
    return result

StrConcat = operations.op('StrConcat', (String, String), String, calc_length=operations.concat_length_calc, bound=False)
Substr = operations.op('Substr', ((int, long), (int, long), String),
                        String, extra_check=operations.substr_check,
                        calc_length=operations.substr_length_calc, bound=False)
StrLen = operations.op('StrLen', String, BV, calc_length=operations.str_strlen_lenght_calc, bound=False)
StrReplace = operations.op('StrReplace', (String, String, String), String,
                        extra_check=operations.str_replace_check,
                        calc_length=operations.str_replace_length_calc, bound=False)

StrContains = operations.op("StrContains", (String, String), Bool, bound=False)

# Equality / inequality check
String.__eq__ = operations.op('__eq__', (String, String), Bool)
String.__ne__ = operations.op('__ne__', (String, String), Bool)

# String manipulation
String.__add__ = operations.op('StrConcat', (String, String), String, calc_length=operations.concat_length_calc, bound=False)
String.Substr = staticmethod(operations.op('Substr', ((int, long), (int, long), String),
                              String, extra_check=operations.substr_check,
                              calc_length=operations.substr_length_calc, bound=False))
String.StrConcat = staticmethod(operations.op('StrConcat', (String, String), String, calc_length=operations.concat_length_calc, bound=False))
String.StrLen = staticmethod(operations.op('StrLen', String, BV, calc_length=operations.str_strlen_lenght_calc, bound=False))
String.StrReplace = staticmethod(operations.op('StrReplace', (String, String, String),
                               String, extra_check=operations.str_replace_check,
                               calc_length=operations.str_replace_length_calc))

String.StrContains = staticmethod(operations.op("StrContains", (String, String), Bool, bound=False))