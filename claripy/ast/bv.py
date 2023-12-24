import logging
import numbers
import weakref

from .bits import Bits
from ..ast.base import _make_name
from .bool import If
from ..utils import deprecated

l = logging.getLogger("claripy.ast.bv")

_bvv_cache = weakref.WeakValueDictionary()


# This is a hilarious hack to get around some sort of bug in z3's python bindings, where
# under some circumstances stuff gets destructed out of order
def cleanup():
    global _bvv_cache  # pylint:disable=global-variable-not-assigned
    del _bvv_cache


import atexit

atexit.register(cleanup)


class BV(Bits):
    """
    A class representing an AST of operations culminating in a bitvector.
    Do not instantiate this class directly, instead use BVS or BVV to construct a symbol or value, and then use
    operations to construct more complicated expressions.

    Individual sub-bits and bit-ranges can be extracted from a bitvector using index and slice notation.
    Bits are indexed weirdly. For a 32-bit AST:

        a[31] is the *LEFT* most bit, so it'd be the 0 in

            01111111111111111111111111111111

        a[0] is the *RIGHT* most bit, so it'd be the 0 in

            11111111111111111111111111111110

        a[31:30] are the two leftmost bits, so they'd be the 0s in:

            00111111111111111111111111111111

        a[1:0] are the two rightmost bits, so they'd be the 0s in:

            11111111111111111111111111111100
    """

    __slots__ = ()

    def chop(self, bits=1):
        """
        Chops a BV into consecutive sub-slices. Obviously, the length of this BV must be a multiple of bits.

        :returns:   A list of smaller bitvectors, each ``bits`` in length. The first one will be the left-most (i.e.
                    most significant) bits.
        """
        s = len(self)
        if s % bits != 0:
            raise ValueError("expression length (%d) should be a multiple of 'bits' (%d)" % (len(self), bits))
        if s == bits:
            return [self]
        else:
            return list(reversed([self[(n + 1) * bits - 1 : n * bits] for n in range(0, s // bits)]))

    def __getitem__(self, rng):
        if type(rng) is slice:
            left = rng.start if rng.start is not None else len(self) - 1
            right = rng.stop if rng.stop is not None else 0
            if left < 0:
                left = len(self) + left
            if right < 0:
                right = len(self) + right
            return Extract(left, right, self)
        else:
            return Extract(int(rng), int(rng), self)

    def get_byte(self, index):
        """
        Extracts a byte from a BV, where the index refers to the byte in a big-endian order

        :param index: the byte to extract
        :return: An 8-bit BV
        """
        pos = (self.size() + 7) // 8 - 1 - index
        if pos < 0:
            raise ValueError(
                "Incorrect index %d. Your index must be between %d and %d." % (index, 0, self.size() // 8 - 1)
            )
        r = self[min(pos * 8 + 7, self.size() - 1) : pos * 8]
        if r.size() % 8 != 0:  # pylint:disable=no-member
            r = r.zero_extend(8 - r.size() % 8)  # pylint:disable=no-member
        return r

    def get_bytes(self, index, size):
        """
        Extracts several bytes from a bitvector, where the index refers to the byte in a big-endian order

        :param index: the byte index at which to start extracting
        :param size: the number of bytes to extract
        :return: A BV of size ``size * 8``
        """
        pos = (self.size() + 7) // 8 - 1 - index
        if pos < 0:
            raise ValueError(
                "Incorrect index %d. Your index must be between %d and %d." % (index, 0, self.size() // 8 - 1)
            )
        if size == 0:
            return BVV(0, 0)
        r = self[min(pos * 8 + 7, self.size() - 1) : (pos - size + 1) * 8]
        if r.size() % 8 != 0:  # pylint:disable=no-member
            r = r.zero_extend(8 - r.size() % 8)  # pylint:disable=no-member
        return r

    def zero_extend(self, n):
        """
        Zero-extends the bitvector by n bits. So:

            a = BVV(0b1111, 4)
            b = a.zero_extend(4)
            b is BVV(0b00001111)
        """
        return ZeroExt(n, self)

    def sign_extend(self, n):
        """
        Sign-extends the bitvector by n bits. So:

            a = BVV(0b1111, 4)
            b = a.sign_extend(4)
            b is BVV(0b11111111)
        """
        return SignExt(n, self)

    def concat(self, *args):
        """
        Concatenates this bitvector with the bitvectors provided.
        This bitvector will be on the far-left, i.e. the most significant bits.
        """
        return Concat(self, *args)

    @staticmethod
    def _from_int(like, value):
        return BVV(value, like.length)

    @staticmethod
    def _from_Bool(like, value):
        return If(value, BVV(1, like.length), BVV(0, like.length))

    @staticmethod
    def _from_bytes(like, value):  # pylint:disable=unused-argument
        return BVV(value)

    @staticmethod
    def _from_str(like, value):  # pylint:disable=unused-argument
        l.warning("BVV value is being coerced from a unicode string, encoding as utf-8")
        value = value.encode("utf-8")
        return BVV(value)

    @staticmethod
    def _from_BVV(like, value):  # pylint:disable=unused-argument
        return BVV(value.value, value.size())

    def val_to_fp(self, sort, signed=True, rm=None):
        """
        Interpret this bitvector as an integer, and return the floating-point representation of that integer.

        :param sort:    The sort of floating point value to return
        :param signed:  Optional: whether this value is a signed integer
        :param rm:      Optional: the rounding mode to use
        :return:        An FP AST whose value is the same as this BV
        """
        if rm is None:
            rm = fp.fp.RM.default()
        if sort is None:
            sort = fp.fp.FSort.from_size(self.length)

        op = fp.fpToFP if signed else fp.fpToFPUnsigned
        return op(rm, self, sort)

    def raw_to_fp(self):
        """
        Interpret the bits of this bitvector as an IEEE754 floating point number.
        The inverse of this function is raw_to_bv.

        :return:        An FP AST whose bit-pattern is the same as this BV
        """
        sort = fp.fp.FSort.from_size(self.length)
        return fp.fpToFP(self, sort)

    def raw_to_bv(self):
        """
        A counterpart to FP.raw_to_bv - does nothing and returns itself.
        """
        return self

    def to_bv(self):
        return self.raw_to_bv()


def BVS(
    name,
    size,
    min=None,
    max=None,
    stride=None,
    uninitialized=False,  # pylint:disable=redefined-builtin
    explicit_name=None,
    discrete_set=False,
    discrete_set_max_card=None,
    **kwargs,
) -> BV:
    """
    Creates a bit-vector symbol (i.e., a variable).

    If you want to specify the maximum or minimum value of a normal symbol that is not part of value-set analysis, you
    should manually add constraints to that effect. **Do not use ``min`` and ``max`` for symbolic execution.**

    :param name:            The name of the symbol.
    :param size:            The size (in bits) of the bit-vector.
    :param min:             The minimum value of the symbol, used only for value-set analysis
    :param max:             The maximum value of the symbol, used only for value-set analysis
    :param stride:          The stride of the symbol, used only for value-set analysis
    :param uninitialized:   Whether this value should be counted as an "uninitialized" value in the course of an
                            analysis.
    :param bool explicit_name:   If False, an identifier is appended to the name to ensure uniqueness.
    :param bool discrete_set: If True, a DiscreteStridedIntervalSet will be used instead of a normal StridedInterval.
    :param int discrete_set_max_card: The maximum cardinality of the discrete set. It is ignored if discrete_set is set
                                      to False or None.

    :returns:               a BV object representing this symbol.
    """

    if stride == 0 and max != min:
        raise ClaripyValueError("BVSes of stride 0 should have max == min")

    if type(name) is bytes:
        name = name.decode()
    if type(name) is not str:
        raise TypeError("Name value for BVS must be a str, got %r" % type(name))

    n = _make_name(name, size, False if explicit_name is None else explicit_name)
    encoded_name = n.encode()

    if not discrete_set:
        discrete_set_max_card = None

    return BV(
        "BVS",
        (n, min, max, stride, uninitialized, discrete_set, discrete_set_max_card),
        variables={n},
        length=size,
        symbolic=True,
        eager_backends=None,
        uninitialized=uninitialized,
        encoded_name=encoded_name,
        **kwargs,
    )


def BVV(value, size=None, **kwargs) -> BV:
    """
    Creates a bit-vector value (i.e., a concrete value).

    :param value:   The value. Either an integer or a bytestring. If it's the latter, it will be interpreted as the
                    bytes of a big-endian constant.
    :param size:    The size (in bits) of the bit-vector. Optional if you provide a string, required for an integer.

    :returns:       A BV object representing this value.
    """

    if type(value) in (bytes, bytearray, memoryview, str):
        if type(value) is str:
            l.warning("BVV value is a unicode string, encoding as utf-8")
            value = value.encode("utf-8")

        if size is None:
            size = len(value) * 8
        elif type(size) is not int:
            raise TypeError("Bitvector size  must be either absent (implicit) or an integer")
        elif size != len(value) * 8:
            raise ClaripyValueError("string/size mismatch for BVV creation")

        value = int.from_bytes(value, "big")

    elif size is None or (type(value) is not int and value is not None):
        raise TypeError("BVV() takes either an integer value and a size or a string of bytes")

    # ensure the 0 <= value < (1 << size)
    # FIXME hack to handle None which is used for an Empty Strided Interval (ESI)
    if value is not None:
        value &= (1 << size) - 1

    if not kwargs:
        try:
            return _bvv_cache[(value, size)]
        except KeyError:
            pass

    result = BV("BVV", (value, size), length=size, **kwargs)
    _bvv_cache[(value, size)] = result
    return result


def SI(
    name=None,
    bits=0,
    lower_bound=None,
    upper_bound=None,
    stride=None,
    to_conv=None,
    explicit_name=None,
    discrete_set=False,
    discrete_set_max_card=None,
):
    name = "unnamed" if name is None else name
    if to_conv is not None:
        si = vsa.CreateStridedInterval(
            name=name, bits=bits, lower_bound=lower_bound, upper_bound=upper_bound, stride=stride, to_conv=to_conv
        )
        return BVS(
            name, si._bits, min=si._lower_bound, max=si._upper_bound, stride=si._stride, explicit_name=explicit_name
        )
    return BVS(
        name,
        bits,
        min=lower_bound,
        max=upper_bound,
        stride=stride,
        explicit_name=explicit_name,
        discrete_set=discrete_set,
        discrete_set_max_card=discrete_set_max_card,
    )


def TSI(bits, name=None, uninitialized=False, explicit_name=None):
    name = "unnamed" if name is None else name
    return BVS(name, bits, uninitialized=uninitialized, explicit_name=explicit_name)


def ESI(bits, **kwargs):
    return BVV(None, bits, **kwargs)


def ValueSet(bits, region=None, region_base_addr=None, value=None, name=None, val=None):
    # Backward compatibility
    if value is None and val is not None:
        value = val
    if region_base_addr is None:
        region_base_addr = 0

    v = region_base_addr + value

    # Backward compatibility
    if isinstance(v, numbers.Number):
        min_v, max_v = v, v
        stride = 0
    elif isinstance(v, vsa.StridedInterval):
        min_v, max_v = v.lower_bound, v.upper_bound
        stride = v.stride
    else:
        raise ClaripyValueError("ValueSet() does not take `value` of type %s" % type(value))

    if name is None:
        name = "ValueSet"
    bvs = BVS(name, bits, min=region_base_addr + min_v, max=region_base_addr + max_v, stride=stride)

    # Annotate the bvs and return the new AST
    vs = bvs.annotate(vsa.RegionAnnotation(region, region_base_addr, value))
    return vs


VS = ValueSet


def DSIS(
    name=None, bits=0, lower_bound=None, upper_bound=None, stride=None, explicit_name=None, to_conv=None, max_card=None
):
    if to_conv is not None:
        si = vsa.CreateStridedInterval(bits=to_conv.size(), to_conv=to_conv)
        return SI(
            name=name,
            bits=si._bits,
            lower_bound=si._lower_bound,
            upper_bound=si._upper_bound,
            stride=si._stride,
            explicit_name=explicit_name,
            discrete_set=True,
            discrete_set_max_card=max_card,
        )
    else:
        return SI(
            name=name,
            bits=bits,
            lower_bound=lower_bound,
            upper_bound=upper_bound,
            stride=stride,
            explicit_name=explicit_name,
            discrete_set=True,
            discrete_set_max_card=max_card,
        )


#
# Unbound operations
#

from .bool import Bool
from .. import operations

# comparisons
ULT = operations.op("__lt__", (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)
ULE = operations.op("__le__", (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)
UGT = operations.op("__gt__", (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)
UGE = operations.op("__ge__", (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)
SLT = operations.op("SLT", (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)
SLE = operations.op("SLE", (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)
SGT = operations.op("SGT", (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)
SGE = operations.op("SGE", (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)

# division
SDiv = operations.op(
    "SDiv",
    (BV, BV),
    BV,
    extra_check=operations.length_same_check,
    bound=False,
    calc_length=operations.basic_length_calc,
)
SMod = operations.op(
    "SMod",
    (BV, BV),
    BV,
    extra_check=operations.length_same_check,
    bound=False,
    calc_length=operations.basic_length_calc,
)

# bit stuff
LShR = operations.op(
    "LShR",
    (BV, BV),
    BV,
    extra_check=operations.length_same_check,
    calc_length=operations.basic_length_calc,
    bound=False,
)
SignExt = operations.op(
    "SignExt", (int, BV), BV, extra_check=operations.extend_check, calc_length=operations.ext_length_calc, bound=False
)
ZeroExt = operations.op(
    "ZeroExt", (int, BV), BV, extra_check=operations.extend_check, calc_length=operations.ext_length_calc, bound=False
)
Extract = operations.op(
    "Extract",
    (int, int, BV),
    BV,
    extra_check=operations.extract_check,
    calc_length=operations.extract_length_calc,
    bound=False,
)

Concat = operations.op("Concat", BV, BV, calc_length=operations.concat_length_calc, bound=False)

RotateLeft = operations.op(
    "RotateLeft",
    (BV, BV),
    BV,
    extra_check=operations.length_same_check,
    calc_length=operations.basic_length_calc,
    bound=False,
)
RotateRight = operations.op(
    "RotateRight",
    (BV, BV),
    BV,
    extra_check=operations.length_same_check,
    calc_length=operations.basic_length_calc,
    bound=False,
)
Reverse = operations.op("Reverse", (BV,), BV, calc_length=operations.basic_length_calc, bound=False)

union = operations.op(
    "union",
    (BV, BV),
    BV,
    extra_check=operations.length_same_check,
    calc_length=operations.basic_length_calc,
    bound=False,
)
widen = operations.op(
    "widen",
    (BV, BV),
    BV,
    extra_check=operations.length_same_check,
    calc_length=operations.basic_length_calc,
    bound=False,
)
intersection = operations.op(
    "intersection",
    (BV, BV),
    BV,
    extra_check=operations.length_same_check,
    calc_length=operations.basic_length_calc,
    bound=False,
)

#
# Bound operations
#

BV.__add__ = operations.op(
    "__add__", (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc
)
BV.__radd__ = operations.reversed_op(BV.__add__)
BV.__floordiv__ = operations.op(
    "__floordiv__", (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc
)
BV.__rfloordiv__ = operations.reversed_op(BV.__floordiv__)
BV.__truediv__ = deprecated("BV.__floordiv__", "BV.__truediv__")(BV.__floordiv__)
BV.__rtruediv__ = deprecated("BV.__rfloordiv__", "BV.__rtruediv__")(BV.__rfloordiv__)
BV.__mul__ = operations.op(
    "__mul__", (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc
)
BV.__rmul__ = operations.reversed_op(BV.__mul__)
BV.__sub__ = operations.op(
    "__sub__", (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc
)
BV.__rsub__ = operations.reversed_op(BV.__sub__)
BV.__pow__ = operations.op(
    "__pow__", (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc
)
BV.__rpow__ = operations.reversed_op(BV.__pow__)
BV.__mod__ = operations.op(
    "__mod__", (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc
)
BV.__rmod__ = operations.reversed_op(BV.__mod__)
BV.SDiv = operations.op(
    "SDiv",
    (BV, BV),
    BV,
    extra_check=operations.length_same_check,
    bound=False,
    calc_length=operations.basic_length_calc,
)
BV.SMod = operations.op(
    "SMod",
    (BV, BV),
    BV,
    extra_check=operations.length_same_check,
    bound=False,
    calc_length=operations.basic_length_calc,
)

BV.__neg__ = operations.op("__neg__", (BV,), BV, calc_length=operations.basic_length_calc)
BV.__pos__ = lambda x: x
BV.__abs__ = operations.op("__abs__", (BV,), BV, calc_length=operations.basic_length_calc)

BV.__eq__ = operations.op("__eq__", (BV, BV), Bool, extra_check=operations.length_same_check)
BV.__ne__ = operations.op("__ne__", (BV, BV), Bool, extra_check=operations.length_same_check)
BV.__ge__ = operations.op("__ge__", (BV, BV), Bool, extra_check=operations.length_same_check)
BV.__le__ = operations.op("__le__", (BV, BV), Bool, extra_check=operations.length_same_check)
BV.__gt__ = operations.op("__gt__", (BV, BV), Bool, extra_check=operations.length_same_check)
BV.__lt__ = operations.op("__lt__", (BV, BV), Bool, extra_check=operations.length_same_check)
BV.SLT = operations.op("SLT", (BV, BV), Bool, extra_check=operations.length_same_check)
BV.SGT = operations.op("SGT", (BV, BV), Bool, extra_check=operations.length_same_check)
BV.SLE = operations.op("SLE", (BV, BV), Bool, extra_check=operations.length_same_check)
BV.SGE = operations.op("SGE", (BV, BV), Bool, extra_check=operations.length_same_check)
BV.ULT = operations.op("__lt__", (BV, BV), Bool, extra_check=operations.length_same_check)
BV.UGT = operations.op("__gt__", (BV, BV), Bool, extra_check=operations.length_same_check)
BV.ULE = operations.op("__le__", (BV, BV), Bool, extra_check=operations.length_same_check)
BV.UGE = operations.op("__ge__", (BV, BV), Bool, extra_check=operations.length_same_check)

BV.__invert__ = operations.op("__invert__", (BV,), BV, calc_length=operations.basic_length_calc)
BV.__or__ = operations.op(
    "__or__", (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc
)
BV.__ror__ = operations.reversed_op(BV.__or__)
BV.__and__ = operations.op(
    "__and__", (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc
)
BV.__rand__ = operations.reversed_op(BV.__and__)
BV.__xor__ = operations.op(
    "__xor__", (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc
)
BV.__rxor__ = operations.reversed_op(BV.__xor__)
BV.__lshift__ = operations.op(
    "__lshift__", (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc
)
BV.__rlshift__ = operations.reversed_op(BV.__lshift__)
BV.__rshift__ = operations.op(
    "__rshift__", (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc
)
BV.__rrshift__ = operations.reversed_op(BV.__rshift__)
BV.LShR = operations.op(
    "LShR", (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc
)

BV.Extract = staticmethod(
    operations.op(
        "Extract",
        (int, int, BV),
        BV,
        extra_check=operations.extract_check,
        calc_length=operations.extract_length_calc,
        bound=False,
    )
)
BV.Concat = staticmethod(operations.op("Concat", BV, BV, calc_length=operations.concat_length_calc, bound=False))
BV.reversed = property(operations.op("Reverse", (BV,), BV, calc_length=operations.basic_length_calc))

BV.union = operations.op(
    "union", (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc
)
BV.widen = operations.op(
    "widen", (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc
)
BV.intersection = operations.op(
    "intersection", (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc
)

from . import fp
from .. import vsa
from ..errors import ClaripyValueError
