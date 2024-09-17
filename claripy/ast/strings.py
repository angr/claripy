from __future__ import annotations

from claripy import operations
from claripy.ast.base import _make_name

from .bits import Bits
from .bool import Bool
from .bv import BV, BVS, BVV


class String(Bits):
    """
    Base class that represent the AST of a String object and implements all the operation useful to create and modify the AST.

    Do not instantiate this class directly, instead use StringS or StringV to construct a symbol or value, and then use
    operations to construct more complicated expressions.
    """

    __slots__ = ("string_length",)

    # Identifier used by composite solver in order to identify if a certain constraints contains
    # variables of type string... In this case cvc4 would handle the solving part.
    #
    # TODO: Find a smarter way to do this!
    STRING_TYPE_IDENTIFIER = "STRING_"
    GENERATED_BVS_IDENTIFIER = "BVS_"
    MAX_LENGTH = 10000

    def __init__(self, *args, length: int, **kwargs):
        """
        :param length: The string bit length
        """
        super().__init__(*args, length=length, **kwargs)
        self.string_length: int = self.length // 8

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
    # TODO: Figure out what to convert here
    #
    # The use case that i found useful here is during the concretization
    # of a symbolic address in memory.
    # When angr has to do this it creates a claripy.If constraints in this form
    # If(condition, <value_read_if_condition_true>, <value_read_if_condition_false>).
    # In some case <value_read_if_condition_false> can be MEM_UNINITIALIZED expressed as BVV
    #
    # What should we return in this case?
    def _from_BV(like, value):  # pylint: disable=unused-argument
        return value

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

    def raw_to_bv(self):
        """
        A counterpart to FP.raw_to_bv - does nothing and returns itself.
        """
        if self.symbolic:
            return BVS(
                next(iter(self.variables)).replace(self.STRING_TYPE_IDENTIFIER, self.GENERATED_BVS_IDENTIFIER),
                self.length,
            )
        return BVV(ord(self.args[0]), self.length)

    def raw_to_fp(self):
        return self.raw_to_bv().raw_to_fp()


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
    n = _make_name(String.STRING_TYPE_IDENTIFIER + name, size, False if explicit_name is None else explicit_name)
    return String(
        "StringS",
        n,
        length=8 * size,
        symbolic=True,
        uninitialized=uninitialized,
        variables=frozenset((n,)),
        **kwargs,
    )


def StringV(value, length: int | None = None, **kwargs):
    """
    Create a new Concrete string (analogous to z3.StringVal())

    :param value:  The constant value of the concrete string
    :param length: The byte length of the string

    :returns:      The String object representing the concrete string
    """

    if length is None:
        length = len(value)

    if length < len(value):
        raise ValueError("Can't make a concrete string value longer than the specified length!")

    return String("StringV", (value, length), length=8 * length, **kwargs)


StrConcat = operations.op("StrConcat", String, String, calc_length=operations.str_concat_length_calc)
StrSubstr = operations.op("StrSubstr", (BV, BV, String), String, calc_length=operations.substr_length_calc)
StrLen = operations.op("StrLen", (String, int), BV, calc_length=operations.strlen_bv_size_calc)
StrReplace = operations.op(
    "StrReplace",
    (String, String, String),
    String,
    extra_check=operations.str_replace_check,
    calc_length=operations.str_replace_length_calc,
)
StrContains = operations.op("StrContains", (String, String), Bool)
StrPrefixOf = operations.op("StrPrefixOf", (String, String), Bool)
StrSuffixOf = operations.op("StrSuffixOf", (String, String), Bool)
StrIndexOf = operations.op("StrIndexOf", (String, String, BV, int), BV, calc_length=operations.strindexof_bv_size_calc)
StrToInt = operations.op("StrToInt", (String, int), BV, calc_length=operations.strtoint_bv_size_calc)
IntToStr = operations.op("IntToStr", (BV,), String, calc_length=operations.int_to_str_length_calc)
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
