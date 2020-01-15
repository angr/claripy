from .bits import Bits
from ..ast.base import _make_name

from .. import operations
from .bool import Bool
from .bv import BV, BVS, BVV


class String(Bits):
    """
    Base class that represent the AST of a String object and implements all the operation useful to create and modify the AST.

    Do not instantiate this class directly, instead use StringS or StringV to construct a symbol or value, and then use
    operations to construct more complicated expressions.
    """

    __slots__ = ('string_length',)

    # Identifier used by composite solver in order to identify if a certain constraints contains
    # variables of type string... In this case cvc4 would handle the solving part.
    #
    # TODO: Find a smarter way to do this!
    STRING_TYPE_IDENTIFIER = 'STRING_'
    GENERATED_BVS_IDENTIFIER = 'BVS_'
    MAX_LENGTH = 10000

    def __init__(self, *args, **kwargs):
        str_len = kwargs['length']
        kwargs['length'] *= 8
        super(String, self).__init__(*args, **kwargs)
        self.string_length = str_len

    def __getitem__(self, rng):
        if type(rng) is slice:
            high = rng.start // 8 if rng.start is not None else self.string_length - 1
            low = rng.stop // 8 if rng.stop is not None else 0
            if high < 0:
                high = self.string_length + high
            if low < 0:
                low = self.string_length + low

            # Because we are indexing from the end, what was high becomes low and vice-versa
            high_str_idx = self.string_length - 1 - low
            low_str_idx = self.string_length - 1 - high
            return StrExtract(low_str_idx, high_str_idx + 1 - low_str_idx, self)
        else:
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
    def _from_BV(like, value): # pylint: disable=unused-argument
        return value

    @staticmethod
    def _from_str(like, value):
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
            return BVS(next(iter(self.variables)).replace(self.STRING_TYPE_IDENTIFIER, self.GENERATED_BVS_IDENTIFIER), self.length)
        else:
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
    result = String("StringS", (n, uninitialized), length=size, symbolic=True, eager_backends=None, uninitialized=uninitialized, variables={n}, **kwargs)
    return result

def StringV(value, length=None, **kwargs):
    """
    Create a new Concrete string (analogous to z3.StringVal())

    :param value: The constant value of the concrete string

    :returns:                    The String object representing the concrete string
    """

    if length is None:
        length = len(value)

    if length < len(value):
        raise ValueError("Can't make a concrete string value longer than the specified length!")

    result = String("StringV", (value, len(value)), length=length, **kwargs)
    return result

StrConcat = operations.op('StrConcat', String, String, calc_length=operations.str_concat_length_calc, bound=False)
StrSubstr = operations.op('StrSubstr', (BV, BV, String),
                        String, calc_length=operations.substr_length_calc, bound=False)
StrExtract = operations.op('StrExtract', (int, int, String),
                              String, extra_check=operations.str_extract_check,
                              calc_length=operations.str_extract_length_calc, bound=False)
StrLen = operations.op('StrLen', (String, int), BV, calc_length=operations.strlen_bv_size_calc, bound=False)
StrReplace = operations.op('StrReplace', (String, String, String), String,
                        extra_check=operations.str_replace_check,
                        calc_length=operations.str_replace_length_calc, bound=False)
StrContains = operations.op("StrContains", (String, String), Bool, bound=False)
StrPrefixOf = operations.op("StrPrefixOf", (String, String), Bool, bound=False)
StrSuffixOf = operations.op("StrSuffixOf", (String, String), Bool, bound=False)
StrIndexOf = operations.op("StrIndexOf", (String, String, BV, int), BV, calc_length=operations.strindexof_bv_size_calc, bound=False)
StrToInt = operations.op("StrToInt", (String, int), BV, calc_length=operations.strtoint_bv_size_calc, bound=False)
IntToStr = operations.op("IntToStr", (BV,), String, calc_length=operations.int_to_str_length_calc, bound=False)
StrIsDigit = operations.op("StrIsDigit", (String,), Bool, bound=False)
UnitStr = operations.op("UnitStr", (BV,), String, bound=False) # convert BV to single-char string

# Equality / inequality check
String.__eq__ = operations.op('__eq__', (String, String), Bool)
String.__ne__ = operations.op('__ne__', (String, String), Bool)

# String manipulation
String.__add__ = StrConcat
String.StrSubstr = staticmethod(StrSubstr)
String.StrExtract = staticmethod(StrExtract)
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
String.UnitStr = staticmethod(UnitStr)
