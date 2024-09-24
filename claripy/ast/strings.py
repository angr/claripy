from __future__ import annotations

from claripy import operations

from .base import Base, _make_name
from .bool import Bool
from .bv import BV


class String(Base):
    """
    Base class that represent the AST of a String object and implements all the operation useful to create and modify the AST.

    Do not instantiate this class directly, instead use StringS or StringV to construct a symbol or value, and then use
    operations to construct more complicated expressions.
    """

    __slots__ = ()

    def __getitem__(self, rng):
        """
        This is a big endian indexer that takes its arguments as bits but returns bytes.
        Returns the range of bits in self defined by: [rng.start, rng.end], indexed from the end
        The bit range may not internally divide any bytes; i.e. low and (high+1) must both be divisible by 8
        Examples:
            self[7:0]  -- returns the last byte of self
            self[15:0] -- returns the last two bytes of self
            self[8:0]  -- Error! [8:0] is 9 bits, it asks for individual bits of the second to last byte!
            self[8:1]  -- Error! [8:1] asks for 1 bit from the second to last byte and 7 from the last byte!
        """
        if type(rng) is slice:
            bits_low = rng.start if rng.start is not None else 0
            bits_high = rng.stop if rng.stop is not None else 8 * (self.string_length - 1)
            if bits_high % 8 != 0 or (bits_low + 1) % 8 != 0:
                raise ValueError("Bit indicies must not internally divide bytes!")
            # high / low form a reverse-indexed byte index
            high = bits_high // 8
            low = bits_low // 8
            if high < 0:
                high = self.string_length + high
            if low < 0:
                low = self.string_length + low
            # StrSubstr takes a front-indexed byte index as a starting point, and a length
            start_idx = self.string_length - 1 - low
            if high > low:
                return StrSubstr(start_idx, 0, self)
            return StrSubstr(start_idx, 1 + low - high, self)
        raise ValueError("Only slices allowed for string extraction")

    @staticmethod
    def _from_str(like, value):  # pylint: disable=unused-argument
        return StringV(value)

    def strReplace(self, str_to_replace, replacement):
        """
        Replace the first occurence of str_to_replace with replacement

        :param claripy.ast.String str_to_replace: pattern that has to be replaced
        :param claripy.ast.String replacement: replacement pattern
        """
        return StrReplace(self, str_to_replace, replacement)

    def toInt(self, bitlength):
        """
        Convert the string to a bitvector holding the integer
        representation of the string

        :param bitlength: size of the biitvector holding the result
        """
        return StrToInt(self, bitlength)

    def indexOf(self, pattern, start_idx, bitlength):
        """
        Return the start index of the pattern inside the input string in a
        Bitvector representation, otherwise it returns -1 (always using a BitVector)

        :param bitlength: size of the biitvector holding the result
        """
        return StrIndexOf(self, pattern, start_idx, bitlength)


def StringS(name, uninitialized=False, explicit_name=False, **kwargs):
    """
    Create a new symbolic string (analogous to z3.String())

    :param name:                 The name of the symbolic string (i. e. the name of the variable)
    :param uninitialized:        Whether this value should be counted as an "uninitialized" value in the course of an
                                 analysis.
    :param bool explicit_name:   If False, an identifier is appended to the name to ensure uniqueness.

    :returns:                    The String object representing the symbolic string
    """
    n = _make_name(name, 0, False if explicit_name is None else explicit_name)
    return String(
        "StringS",
        (n,),
        symbolic=True,
        uninitialized=uninitialized,
        variables=frozenset((n,)),
        **kwargs,
    )


def StringV(value, **kwargs):
    """
    Create a new Concrete string (analogous to z3.StringVal())

    :param value:  The constant value of the concrete string

    :returns:      The String object representing the concrete string
    """

    return String("StringV", (value,), **kwargs)


StrConcat = operations.op("StrConcat", String, String)
StrSubstr = operations.op("StrSubstr", (BV, BV, String), String)
StrLen = operations.op("StrLen", (String), BV, calc_length=lambda *_: 64)
StrReplace = operations.op("StrReplace", (String, String, String), String)
StrContains = operations.op("StrContains", (String, String), Bool)
StrPrefixOf = operations.op("StrPrefixOf", (String, String), Bool)
StrSuffixOf = operations.op("StrSuffixOf", (String, String), Bool)
StrIndexOf = operations.op("StrIndexOf", (String, String, BV), BV, calc_length=lambda *_: 64)
StrToInt = operations.op("StrToInt", (String), BV, calc_length=lambda *_: 64)
IntToStr = operations.op("IntToStr", (BV,), String)
StrIsDigit = operations.op("StrIsDigit", (String,), Bool)

# Equality / inequality check
String.__eq__ = operations.op("__eq__", (String, String), Bool)
String.__ne__ = operations.op("__ne__", (String, String), Bool)

# String manipulation
String.__add__ = StrConcat
String.StrSubstr = staticmethod(StrSubstr)
String.StrConcat = staticmethod(StrConcat)
String.StrLen = staticmethod(StrLen)
String.StrReplace = staticmethod(StrReplace)
String.StrContains = staticmethod(StrContains)
String.StrPrefixOf = staticmethod(StrPrefixOf)
String.StrSuffixOf = staticmethod(StrSuffixOf)
String.StrIndexOf = staticmethod(StrIndexOf)
String.StrToInt = staticmethod(StrToInt)
String.StrIsDigit = staticmethod(StrIsDigit)
String.IntToStr = staticmethod(IntToStr)
