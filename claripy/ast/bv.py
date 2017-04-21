from .bits import Bits
from .base import _make_name, make_op, make_reversed_op

import logging
import itertools
l = logging.getLogger("claripy.ast.bv")

_bvv_cache = dict()

# This is a hilarious hack to get around some sort of bug in z3's python bindings, where
# under some circumstances stuff gets destructed out of order
def cleanup():
    global _bvv_cache #pylint:disable=global-variable-not-assigned
    del _bvv_cache
import atexit
atexit.register(cleanup)

class BV(Bits):

    # TODO: do these go on Bits or BV?
    def chop(self, bits=1):
        """
        Chops an AST into ASTs of size 'bits'. Obviously, the length of the AST must be
        a multiple of bits.
        """
        s = len(self)
        if s % bits != 0:
            raise ValueError("expression length (%d) should be a multiple of 'bits' (%d)" % (len(self), bits))
        elif s == bits:
            return [ self ]
        else:
            return list(reversed([ self[(n+1)*bits - 1:n*bits] for n in range(0, s / bits) ]))

    def __getitem__(self, rng):
        """
        Extracts bits from the AST. ASTs are indexed weirdly. For a 32-bit AST:

            a[31] is the *LEFT* most bit, so it'd be the 0 in

                01111111111111111111111111111111

            a[0] is the *RIGHT* most bit, so it'd be the 0 in

                11111111111111111111111111111110

            a[31:30] are the two leftmost bits, so they'd be the 0s in:

                00111111111111111111111111111111

            a[1:0] are the two rightmost bits, so they'd be the 0s in:

                11111111111111111111111111111100

        :return: the new AST.
        """
        if type(rng) is slice:
            left = rng.start if rng.start is not None else len(self)-1
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
        :return:
        """
        pos = self.size() / 8 - 1 - index
        return self[pos * 8 + 7 : pos * 8]

    def get_bytes(self, index, size):
        """
        Extracts several byte from a BV, where the index refers to the byte in a big-endian order
        :param index: the byte to extract
        :return:
        """
        pos = self.size() / 8 - 1 - index
        return self[pos * 8 + 7 : (pos - size + 1) * 8]

    def zero_extend(self, n):
        """
        Zero-extends the AST by n bits. So:

            a = BVV(0b1111, 4)
            b = a.zero_extend(4)
            b is BVV(0b00001111)
        """
        return ZeroExt(n, self)

    def sign_extend(self, n):
        """
        Sign-extends the AST by n bits. So:

            a = BVV(0b1111, 4)
            b = a.sign_extend(4)
            b is BVV(0b11111111)
        """
        return SignExt(n, self)

    def concat(self, *args):
        """
        Concatenates this AST with the ASTs provided.
        """
        return Concat(self, *args)

    @staticmethod
    def _from_int(like, value):
        return BVV(value, like.length)

    @staticmethod
    def _from_long(like, value):
        return BVV(value, like.length)

    @staticmethod
    def _from_str(like, value): #pylint:disable=unused-argument
        return BVV(value)

    @staticmethod
    def _from_BVV(like, value): #pylint:disable=unused-argument
        return BVV(value.value, value.size())

    def signed_to_fp(self, rm, sort):
        if rm is None:
            rm = fp.fp.RM.default()

        return fp.fpToFP(rm, self, sort)

    def unsigned_to_fp(self, rm, sort):
        if rm is None:
            rm = fp.fp.RM.default()
        return fp.fpToFPUnsigned(rm, self, sort)

    def raw_to_fp(self):
        sort = fp.fp.FSort.from_size(self.length)
        return fp.fpToFP(self, sort)

    def to_bv(self):
        return self

def BVS(
    name, length, min=None, max=None, stride=None, uninitialized=False,  #pylint:disable=redefined-builtin
    explicit_name=None, discrete_set=False, discrete_set_max_card=None,
    filters=None
):
    """
    Creates a bit-vector symbol (i.e., a variable).

    :param name:            The name of the symbol.
    :param size:            The size (in bits) of the bit-vector.
    :param min:             The minimum value of the symbol.
    :param max:             The maximum value of the symbol.
    :param stride:          The stride of the symbol.
    :param uninitialized:   Whether this value should be counted as an "uninitialized" value in the course of an
                            analysis.
    :param bool explicit_name:   If False, an identifier is appended to the name to ensure uniqueness.
    :param bool discrete_set: If True, a DiscreteStridedIntervalSet will be used instead of a normal StridedInterval.
    :param int discrete_set_max_card: The maximum cardinality of the discrete set. It is ignored if discrete_set is set
                                      to False or None.
    :param filters:         A list of functions that will be applied to this AST at every operation.

    :returns:               a BV object representing this symbol.
    """

    if stride == 0 and max != min:
        raise ClaripyValueError("BVSes of stride 0 should have max == min")

    n = _make_name(name, length, False if explicit_name is None else explicit_name)

    if not discrete_set:
        discrete_set_max_card = None

    return BV(
        get_structure('BVS', (n, length, min, max, stride, uninitialized, discrete_set, discrete_set_max_card)),
        filters=filters, _eager=False
    )._deduplicate()._apply_filters()

def BVV(value, size=None, filters=None):
    """
    Creates a bit-vector value (i.e., a concrete value).

    :param value:   The value.
    :param size:    The size (in bits) of the bit-vector.
    :param filters:         A list of functions that will be applied to this AST at every operation.

    :returns:       A BV object representing this value.
    """

    if type(value) is str or type(value) is unicode:
        if type(value) is unicode:
            l.warn("BVV value is a unicode string")
        if size is None:
            size = 8*len(value)
            value = int(value.encode('hex'), 16) if value != "" else 0
        elif size == len(value)*8:
            value = int(value.encode('hex'), 16) if value != "" else 0
        else:
            raise ClaripyValueError('string/size mismatch for BVV creation')
    elif size is None:
        raise ClaripyValueError('BVV() takes either an integer value and a size or a string of bytes')

    # ensure the 0 <= value < (1 << size)
    # FIXME hack to handle None which is used for an Empty Strided Interval (ESI)
    if value is not None:
        value &= (1 << size) -1

    try:
        return _bvv_cache[(value, size)]
    except KeyError:
        pass
    result = BV(get_structure('BVV', (value, size)), filters=filters)._deduplicate()._apply_filters()
    _bvv_cache[(value, size)] = result
    return result

def SI(name=None, bits=0, lower_bound=None, upper_bound=None, stride=None, to_conv=None, explicit_name=None,
       discrete_set=False, discrete_set_max_card=None):
    name = 'unnamed' if name is None else name
    if to_conv is not None:
        si = vsa.CreateStridedInterval(name=name, bits=bits, lower_bound=lower_bound, upper_bound=upper_bound, stride=stride, to_conv=to_conv)
        return BVS(name, si._bits, min=si._lower_bound, max=si._upper_bound, stride=si._stride, explicit_name=explicit_name)
    return BVS(name, bits, min=lower_bound, max=upper_bound, stride=stride, explicit_name=explicit_name,
               discrete_set=discrete_set, discrete_set_max_card=discrete_set_max_card)

def TSI(bits, name=None, uninitialized=False, explicit_name=None):
    name = 'unnamed' if name is None else name
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
    if isinstance(v, (int, long)):
        min_v, max_v = v, v
        stride = 0
    elif isinstance(v, vsa.StridedInterval):
        min_v, max_v = v.lower_bound, v.upper_bound
        stride = v.stride
    else:
        raise ClaripyValueError("ValueSet() does not take `value` of type %s" % type(value))

    bvs = BVS(name, bits, min=region_base_addr + min_v, max=region_base_addr + max_v, stride=stride)

    # Annotate the bvs and return the new AST
    vs = bvs.annotate_inline(vsa.RegionAnnotation(region, region_base_addr, value))
    return vs

VS = ValueSet

def DSIS(name=None, bits=0, lower_bound=None, upper_bound=None, stride=None, explicit_name=None, to_conv=None, max_card=None):

    if to_conv is not None:
        si = vsa.CreateStridedInterval(bits=to_conv.size(), to_conv=to_conv)
        return SI(name=name, bits=si._bits, lower_bound=si._lower_bound, upper_bound=si._upper_bound, stride=si._stride,
                   explicit_name=explicit_name, discrete_set=True, discrete_set_max_card=max_card)
    else:
        return SI(name=name, bits=bits, lower_bound=lower_bound, upper_bound=upper_bound, stride=stride,
                   explicit_name=explicit_name, discrete_set=True, discrete_set_max_card=max_card)

#
# Unbound operations
#

from .bool import Bool

# comparisons
ULT = make_op('__lt__', (BV, BV), Bool)
ULE = make_op('__le__', (BV, BV), Bool)
UGT = make_op('__gt__', (BV, BV), Bool)
UGE = make_op('__ge__', (BV, BV), Bool)
SLT = make_op('SLT', (BV, BV), Bool)
SLE = make_op('SLE', (BV, BV), Bool)
SGT = make_op('SGT', (BV, BV), Bool)
SGE = make_op('SGE', (BV, BV), Bool)

# division
SDiv = make_op('SDiv', (BV, BV), BV)
SMod = make_op('SMod', (BV, BV), BV)

# bit stuff
LShR = make_op('LShR', (BV, BV), BV)
SignExt = make_op('SignExt', ((int, long), BV), BV)
ZeroExt = make_op('ZeroExt', ((int, long), BV), BV)
Extract = make_op('Extract', ((int, long), (int, long), BV), BV)

Concat = make_op('Concat', BV, BV)

RotateLeft = make_op('RotateLeft', (BV, BV), BV)
RotateRight = make_op('RotateRight', (BV, BV), BV)
Reverse = make_op('Reverse', (BV,), BV)

union_counter = itertools.count()
def _union_postprocessor(union_expression):
    new_name = 'union_%d' % next(union_counter)
    va = VariableAnnotation(frozenset((new_name,)))
    return union_expression.annotate_outer(va)

union = make_op('union', (BV, BV), BV, expression_postprocessor=_union_postprocessor)
widen = make_op('widen', (BV, BV), BV)
intersection = make_op('intersection', (BV, BV), BV)

#
# Bound operations
#

BV.__add__ = make_op('__add__', (BV, BV), BV)
BV.__radd__ = make_reversed_op(BV.__add__.im_func)
BV.__div__ = make_op('__div__', (BV, BV), BV)
BV.__rdiv__ = make_reversed_op(BV.__div__.im_func)
BV.__truediv__ = make_op('__truediv__', (BV, BV), BV)
BV.__rtruediv__ = make_reversed_op(BV.__truediv__.im_func)
BV.__floordiv__ = make_op('__floordiv__', (BV, BV), BV)
BV.__rfloordiv__ = make_reversed_op(BV.__floordiv__.im_func)
BV.__mul__ = make_op('__mul__', (BV, BV), BV)
BV.__rmul__ = make_reversed_op(BV.__mul__.im_func)
BV.__sub__ = make_op('__sub__', (BV, BV), BV)
BV.__rsub__ = make_reversed_op(BV.__sub__.im_func)
BV.__pow__ = make_op('__pow__', (BV, BV), BV)
BV.__rpow__ = make_reversed_op(BV.__pow__.im_func)
BV.__mod__ = make_op('__mod__', (BV, BV), BV)
BV.__rmod__ = make_reversed_op(BV.__mod__.im_func)
BV.__divmod__ = make_op('__divmod__', (BV, BV), BV)
BV.__rdivmod__ = make_reversed_op(BV.__divmod__.im_func)
BV.SDiv = make_op('SDiv', (BV, BV), BV)
BV.SMod = make_op('SMod', (BV, BV), BV)

BV.__neg__ = make_op('__neg__', (BV,), BV)
BV.__pos__ = make_op('__pos__', (BV,), BV)
BV.__abs__ = make_op('__abs__', (BV,), BV)

BV.__eq__ = make_op('__eq__', (BV, BV), Bool)
BV.__ne__ = make_op('__ne__', (BV, BV), Bool)
BV.__ge__ = make_op('UGE', (BV, BV), Bool)
BV.__le__ = make_op('ULE', (BV, BV), Bool)
BV.__gt__ = make_op('UGT', (BV, BV), Bool)
BV.__lt__ = make_op('ULT', (BV, BV), Bool)
BV.SLT = make_op('SLT', (BV, BV), Bool)
BV.SGT = make_op('SGT', (BV, BV), Bool)
BV.SLE = make_op('SLE', (BV, BV), Bool)
BV.SGE = make_op('SGE', (BV, BV), Bool)
BV.ULT = make_op('ULT', (BV, BV), Bool)
BV.UGT = make_op('UGT', (BV, BV), Bool)
BV.ULE = make_op('ULE', (BV, BV), Bool)
BV.UGE = make_op('UGE', (BV, BV), Bool)

BV.__invert__ = make_op('__invert__', (BV,), BV)
BV.__or__ = make_op('__or__', (BV, BV), BV)
BV.__ror__ = make_reversed_op(BV.__or__.im_func)
BV.__and__ = make_op('__and__', (BV, BV), BV)
BV.__rand__ = make_reversed_op(BV.__and__.im_func)
BV.__xor__ = make_op('__xor__', (BV, BV), BV)
BV.__rxor__ = make_reversed_op(BV.__xor__.im_func)
BV.__lshift__ = make_op('__lshift__', (BV, BV), BV)
BV.__rlshift__ = make_reversed_op(BV.__lshift__.im_func)
BV.__rshift__ = make_op('__rshift__', (BV, BV), BV)
BV.__rrshift__ = make_reversed_op(BV.__rshift__.im_func)
BV.LShR = make_op('LShR', (BV, BV), BV)

BV.Extract = staticmethod(make_op('Extract', ((int, long), (int, long), BV), BV))
BV.Concat = staticmethod(make_op('Concat', BV, BV))
BV.reversed = property(make_op('Reverse', (BV,), BV))

BV.union = make_op('union', (BV, BV), BV, structure_postprocessor=_union_postprocessor)
BV.widen = make_op('widen', (BV, BV), BV)
BV.intersection = make_op('intersection', (BV, BV), BV)

from . import fp
from .. import vsa
from ..errors import ClaripyValueError
from .structure import get_structure
from ..annotations import VariableAnnotation
