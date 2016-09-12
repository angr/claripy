from .bits import Bits
from ..ast.base import _make_name

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

def BVS(name, size, min=None, max=None, stride=None, uninitialized=False,  #pylint:disable=redefined-builtin
        explicit_name=None, discrete_set=False, discrete_set_max_card=None, **kwargs):
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

    :returns:               a BV object representing this symbol.
    """

    if stride == 0 and max != min:
        raise ClaripyValueError("BVSes of stride 0 should have max == min")

    n = _make_name(name, size, False if explicit_name is None else explicit_name)

    if not discrete_set:
        discrete_set_max_card = None

    return BV('BVS', (n, min, max, stride, uninitialized, discrete_set, discrete_set_max_card), variables={n},
              length=size, symbolic=True, eager_backends=None, uninitialized=uninitialized, **kwargs)

def BVV(value, size=None, **kwargs):
    """
    Creates a bit-vector value (i.e., a concrete value).

    :param value:   The value.
    :param size:    The size (in bits) of the bit-vector.

    :returns:       A BV object representing this value.
    """

    if type(value) is str:
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

    if not kwargs:
        try: return _bvv_cache[(value, size)]
        except KeyError: pass

    result = BV('BVV', (value, size), length=size, **kwargs)
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
    vs = bvs.annotate(vsa.RegionAnnotation(region, region_base_addr, value))
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
from .. import operations

# comparisons
ULT = operations.op('__lt__', (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)
ULE = operations.op('__le__', (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)
UGT = operations.op('__gt__', (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)
UGE = operations.op('__ge__', (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)
SLT = operations.op('SLT', (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)
SLE = operations.op('SLE', (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)
SGT = operations.op('SGT', (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)
SGE = operations.op('SGE', (BV, BV), Bool, extra_check=operations.length_same_check, bound=False)

# division
SDiv = operations.op('SDiv', (BV, BV), BV, extra_check=operations.length_same_check, bound=False, calc_length=operations.basic_length_calc)
SMod = operations.op('SMod', (BV, BV), BV, extra_check=operations.length_same_check, bound=False, calc_length=operations.basic_length_calc)

# bit stuff
LShR = operations.op('LShR', (BV, BV), BV, extra_check=operations.length_same_check,
                     calc_length=operations.basic_length_calc, bound=False)
SignExt = operations.op('SignExt', ((int, long), BV), BV,
                        calc_length=operations.ext_length_calc, bound=False)
ZeroExt = operations.op('ZeroExt', ((int, long), BV), BV,
                        calc_length=operations.ext_length_calc, bound=False)
Extract = operations.op('Extract', ((int, long), (int, long), BV),
                        BV, extra_check=operations.extract_check,
                        calc_length=operations.extract_length_calc, bound=False)

Concat = operations.op('Concat', BV, BV, calc_length=operations.concat_length_calc, bound=False)

RotateLeft = operations.op('RotateLeft', (BV, BV), BV,
                           extra_check=operations.length_same_check,
                           calc_length=operations.basic_length_calc, bound=False)
RotateRight = operations.op('RotateRight', (BV, BV), BV,
                            extra_check=operations.length_same_check,
                            calc_length=operations.basic_length_calc, bound=False)
Reverse = operations.op('Reverse', (BV,), BV,
                        calc_length=operations.basic_length_calc, bound=False)

union = operations.op('union', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc, bound=False)
widen = operations.op('widen', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc, bound=False)
intersection = operations.op('intersection', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc, bound=False)

#
# Bound operations
#

BV.__add__ = operations.op('__add__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__radd__ = operations.reversed_op(BV.__add__.im_func)
BV.__div__ = operations.op('__div__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rdiv__ = operations.reversed_op(BV.__div__.im_func)
BV.__truediv__ = operations.op('__truediv__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rtruediv__ = operations.reversed_op(BV.__truediv__.im_func)
BV.__floordiv__ = operations.op('__floordiv__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rfloordiv__ = operations.reversed_op(BV.__floordiv__.im_func)
BV.__mul__ = operations.op('__mul__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rmul__ = operations.reversed_op(BV.__mul__.im_func)
BV.__sub__ = operations.op('__sub__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rsub__ = operations.reversed_op(BV.__sub__.im_func)
BV.__pow__ = operations.op('__pow__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rpow__ = operations.reversed_op(BV.__pow__.im_func)
BV.__mod__ = operations.op('__mod__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rmod__ = operations.reversed_op(BV.__mod__.im_func)
BV.__divmod__ = operations.op('__divmod__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rdivmod__ = operations.reversed_op(BV.__divmod__.im_func)
BV.SDiv = operations.op('SDiv', (BV, BV), BV, extra_check=operations.length_same_check, bound=False, calc_length=operations.basic_length_calc)
BV.SMod = operations.op('SMod', (BV, BV), BV, extra_check=operations.length_same_check, bound=False, calc_length=operations.basic_length_calc)

BV.__neg__ = operations.op('__neg__', (BV,), BV, calc_length=operations.basic_length_calc)
BV.__pos__ = operations.op('__pos__', (BV,), BV, calc_length=operations.basic_length_calc)
BV.__abs__ = operations.op('__abs__', (BV,), BV, calc_length=operations.basic_length_calc)

BV.__eq__ = operations.op('__eq__', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.__ne__ = operations.op('__ne__', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.__ge__ = operations.op('__ge__', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.__le__ = operations.op('__le__', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.__gt__ = operations.op('__gt__', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.__lt__ = operations.op('__lt__', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.SLT = operations.op('SLT', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.SGT = operations.op('SGT', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.SLE = operations.op('SLE', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.SGE = operations.op('SGE', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.ULT = operations.op('__lt__', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.UGT = operations.op('__gt__', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.ULE = operations.op('__le__', (BV, BV), Bool, extra_check=operations.length_same_check)
BV.UGE = operations.op('__ge__', (BV, BV), Bool, extra_check=operations.length_same_check)

BV.__invert__ = operations.op('__invert__', (BV,), BV, calc_length=operations.basic_length_calc)
BV.__or__ = operations.op('__or__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__ror__ = operations.reversed_op(BV.__or__.im_func)
BV.__and__ = operations.op('__and__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rand__ = operations.reversed_op(BV.__and__.im_func)
BV.__xor__ = operations.op('__xor__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rxor__ = operations.reversed_op(BV.__xor__.im_func)
BV.__lshift__ = operations.op('__lshift__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rlshift__ = operations.reversed_op(BV.__lshift__.im_func)
BV.__rshift__ = operations.op('__rshift__', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.__rrshift__ = operations.reversed_op(BV.__rshift__.im_func)
BV.LShR = operations.op('LShR', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)

BV.Extract = staticmethod(operations.op('Extract', ((int, long), (int, long), BV), BV, extra_check=operations.extract_check, calc_length=operations.extract_length_calc, bound=False))
BV.Concat = staticmethod(operations.op('Concat', BV, BV, calc_length=operations.concat_length_calc, bound=False))
BV.reversed = property(operations.op('Reverse', (BV,), BV, calc_length=operations.basic_length_calc))

BV.union = operations.op('union', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.widen = operations.op('widen', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)
BV.intersection = operations.op('intersection', (BV, BV), BV, extra_check=operations.length_same_check, calc_length=operations.basic_length_calc)

from . import fp
from .. import vsa
from ..errors import ClaripyValueError
