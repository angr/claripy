import fractions
import functools
import math
import itertools
import logging

logger = logging.getLogger('claripy.vsa.strided_interval')

from .decorators import expand_ifproxy
from ..backend_object import BackendObject

def normalize_types(f):
    @functools.wraps(f)
    def normalizer(self, o):
        '''
        Convert any object to an object that we can process.
        '''
        # Special handler for union
        if f.__name__ == 'union' and isinstance(o, DiscreteStridedIntervalSet):
            return o.union(self)

        if isinstance(o, ValueSet) or isinstance(o, IfProxy) or isinstance(o, DiscreteStridedIntervalSet):
            # It should be put to o.__radd__(self) when o is a ValueSet
            return NotImplemented

        if isinstance(o, Base):
            o = o.model
        if isinstance(self, Base):
            self = o.model
        if type(self) is BVV:
            self = self.value
        if type(o) is BVV:
            o = o.value
        if type(o) in (int, long):
            o = StridedInterval(bits=StridedInterval.min_bits(o), stride=0, lower_bound=o, upper_bound=o)
        if type(self) in (int, long):
            self = StridedInterval(bits=StridedInterval.min_bits(self), stride=0, lower_bound=self, upper_bound=self)

        if f.__name__ not in ('concat', ):
            # Make sure they have the same length
            common_bits = max(o.bits, self.bits)
            if o.bits < common_bits:
                o = o.zero_extend(common_bits)
            if self.bits < common_bits:
                self = self.zero_extend(common_bits)

        self_reversed = False

        if self._reversed != o._reversed:
            # We are working on two instances that have different endianness!
            # Make sure the `reversed` property of self is kept the same after operation
            if self._reversed:
                self_reversed = True
                self = self.copy()
                self._reversed = False

            else:
                # If self is an integer, we wanna reverse self as well
                if self.is_integer:
                    self = self._reverse()
                    self_reversed = True
                else:
                    o = o._reverse()

        ret = f(self, o)
        if self_reversed and isinstance(ret, StridedInterval):
            ret = ret.reverse()
        return ret

    return normalizer

si_id_ctr = itertools.count()

# Whether DiscreteStridedIntervalSet should be used or not. Sometimes we manually set it to False to allow easy
# implementation of test cases.
allow_dsis = False

class StridedInterval(BackendObject):
    """
    A Strided Interval is represented in the following form:
        bits,stride[lower_bound, upper_bound]
    For more details, please refer to relevant papers like TIE and WYSINWYE.

    This implementation is signedness-agostic, please refer to _Signedness-Agnostic Program Analysis: Precise Integer
    Bounds for Low-Level Code_ by Jorge A. Navas, etc. for more details.

    Thanks all corresponding authors for their outstanding works.
    """
    def __init__(self, name=None, bits=0, stride=None, lower_bound=None, upper_bound=None, uninitialized=False, bottom=False):
        self._name = name

        if self._name is None:
            self._name = "SI_%d" % si_id_ctr.next()

        self._bits = bits
        self._stride = stride
        self._lower_bound = lower_bound
        self._upper_bound = upper_bound

        if lower_bound is not None and type(lower_bound) not in (int, long):
            raise ClaripyVSAError("'lower_bound' must be an int or a long. %s is not supported." % type(lower_bound))

        if upper_bound is not None and type(upper_bound) not in (int, long):
            raise ClaripyVSAError("'upper_bound' must be an int or a long. %s is not supported." % type(upper_bound))

        self._reversed = False

        self._is_bottom = bottom

        self.uninitialized = uninitialized

        if self._upper_bound is not None and bits == 0:
            self._bits = self._min_bits()

        if self._upper_bound is None:
            self._upper_bound = StridedInterval.max_int(self.bits)

        if self._lower_bound is None:
            self._lower_bound = StridedInterval.min_int(self.bits)

        # For lower bound and upper bound, we always store the unsigned version
        self._lower_bound = self._lower_bound & (2 ** bits - 1)
        self._upper_bound = self._upper_bound & (2 ** bits - 1)

        self.normalize()

    def copy(self):
        si = StridedInterval(name=self._name,
                             bits=self.bits,
                             stride=self.stride,
                             lower_bound=self.lower_bound,
                             upper_bound=self.upper_bound,
                             uninitialized=self.uninitialized,
                             bottom=self._is_bottom)
        si._reversed = self._reversed
        return si

    def nameless_copy(self):
        si = StridedInterval(name=None,
                             bits=self.bits,
                             stride=self.stride,
                             lower_bound=self.lower_bound,
                             upper_bound=self.upper_bound,
                             uninitialized=self.uninitialized,
                             bottom=self._is_bottom)
        si._reversed = self._reversed
        return si

    def normalize(self):
        if self.bits == 8 and self.reversed:
            self._reversed = False

        if self.is_empty:
            return self

        if self.lower_bound == self.upper_bound:
            self._stride = 0

        if self.lower_bound < 0:
            self.lower_bound = self.lower_bound & (2 ** self.bits - 1)

        self._normalize_top()

        if self._stride < 0:
            raise Exception("Why does this happen?")

        return self

    def eval(self, n, signed=False):
        """
        Evaluate this StridedInterval to obtain a list of concrete integers
        :param n: Upper bound for the number of concrete integers
        :param signed: Treat this StridedInterval as signed or unsigned
        :return: A list of at most `n` concrete integers
        """

        results = [ ]

        if self.is_empty:
            # no value is available
            pass

        elif self.stride == 0 and n > 0:
            results.append(self.lower_bound)
        else:
            if signed:
                # View it as a signed integer
                bounds = self._signed_bounds()

            else:
                # View it as an unsigned integer
                bounds = self._unsigned_bounds()

            for lb, ub in bounds:
                while len(results) < n and lb <= ub:
                    results.append(lb)
                    lb += self.stride # It will not overflow

        return results

    #
    # Private methods
    #

    def __hash__(self):
        return hash((self.bits, self.lower_bound, self.upper_bound, self.stride, self._reversed, self.uninitialized))

    def _normalize_top(self):
        if self.lower_bound == self._modular_add(self.upper_bound, 1, self.bits) and self.stride == 1:
            # This is a TOP!
            # Normalize it
            self.lower_bound = 0
            self.upper_bound = self.max_int(self.bits)

    def _ssplit(self):
        """
        Split `self` at the south pole, which is the same as in unsigned arithmetic

        :return: A list of split StridedIntervals
        """

        south_pole_right = self.max_int(self.bits) # 111...1
        # south_pole_left = 0

        # Is `self` straddling the south pole?
        if self.upper_bound < self.lower_bound:
            # It straddles the south pole!

            a_upper_bound = south_pole_right - ((south_pole_right - self.lower_bound) % self.stride)
            a = StridedInterval(bits=self.bits, stride=self.stride, lower_bound=self.lower_bound, upper_bound=a_upper_bound)

            b_lower_bound = self._modular_add(a_upper_bound, self.stride, self.bits)
            b = StridedInterval(bits=self.bits, stride=self.stride, lower_bound=b_lower_bound, upper_bound=self.upper_bound)

            return [ a, b ]

        else:
            return [ self.copy() ]

    def _nsplit(self):
        """
        Split `self` at the north pole, which is the same as in signed arithmetic

        :return: A list of split StridedIntervals
        """

        north_pole_left = self.max_int(self.bits - 1) # 01111...1
        north_pole_right = 2 ** (self.bits - 1) # 1000...0

        # Is `self` straddling the north pole?
        if self.lower_bound <= north_pole_left and self.upper_bound >= north_pole_right:
            # Yes it does!

            a_upper_bound = north_pole_left - ((north_pole_left - self.lower_bound) % self.stride)
            a = StridedInterval(bits=self.bits, stride=self.stride, lower_bound=self.lower_bound, upper_bound=a_upper_bound)

            b_lower_bound = a_upper_bound + self.stride
            b = StridedInterval(bits=self.bits, stride=self.stride, lower_bound=b_lower_bound, upper_bound=self.upper_bound)

            return [ a, b ]

        else:
            return [ self.copy() ]

    def _psplit(self):
        """
        Split `self` at both north and south poles

        :return: A list of split StridedIntervals
        """

        nsplit_list = self._nsplit()
        psplit_list = [ ]

        for si in nsplit_list:
            psplit_list.extend(si._ssplit())

        return psplit_list

    def _signed_bounds(self):
        """
        Get lower bound and upper bound for `self` in signed arithmetic
        :return: a list  of (lower_bound, upper_bound) tuples
        """

        nsplit = self._nsplit()
        if len(nsplit) == 1:
            lb = nsplit[0].lower_bound
            ub = nsplit[0].upper_bound

            lb = self._unsigned_to_signed(lb, self.bits)
            ub = self._unsigned_to_signed(ub, self.bits)

            return [ (lb, ub) ]

        elif len(nsplit) == 2:
            # nsplit[0] is on the left hemisphere, and nsplit[1] is on the right hemisphere

            # The left one
            lb_1 = nsplit[0].lower_bound
            ub_1 = nsplit[0].upper_bound

            # The right one
            lb_2 = nsplit[1].lower_bound
            ub_2 = nsplit[1].upper_bound
            # Then convert them to negative numbers
            lb_2 = self._unsigned_to_signed(lb_2, self.bits)
            ub_2 = self._unsigned_to_signed(ub_2, self.bits)

            return [ (lb_1, ub_1), (lb_2, ub_2) ]
        else:
            raise Exception('WTF')

    def _unsigned_bounds(self):
        """
        Get lower bound and upper bound for `self` in unsigned arithmetic
        :return: a list of (lower_bound, upper_bound) tuples
        """

        ssplit = self._ssplit()
        if len(ssplit) == 1:
            lb = ssplit[0].lower_bound
            ub = ssplit[0].upper_bound

            return [ (lb, ub) ]
        elif len(ssplit) == 2:
            # ssplit[0] is on the left hemisphere, and ssplit[1] is on the right hemisphere

            lb_1 = ssplit[0].lower_bound
            ub_1 = ssplit[0].upper_bound

            lb_2 = ssplit[1].lower_bound
            ub_2 = ssplit[1].upper_bound

            return [ (lb_1, ub_1), (lb_2, ub_2) ]
        else:
            raise Exception('WTF')

    #
    # Comparison operations
    #

    def identical(self, o):
        """
        Used to make exact comparisons between two StridedIntervals. Usually it is only used in test cases.

        :param o: The other StridedInterval to compare with
        :return: True if they are exactly same, False otherwise
        """

        if (self.bits == o.bits and
                self.stride == o.stride and
                self.lower_bound == o.lower_bound and
                self.upper_bound == o.upper_bound):
            return True

        else:
            return False

    @normalize_types
    def SLT(self, o):
        """
        Signed less than

        :param o: The other operand
        :return: TrueResult(), FalseResult(), or MaybeResult()
        """

        signed_bounds_1 = self._signed_bounds()
        signed_bounds_2 = o._signed_bounds()

        ret = [ ]
        for lb_1, ub_1 in signed_bounds_1:
            for lb_2, ub_2 in signed_bounds_2:
                if ub_1 < lb_2:
                    ret.append(TrueResult())
                elif lb_1 >= ub_2:
                    ret.append(FalseResult())
                else:
                    ret.append(MaybeResult())

        if all([r == TrueResult() for r in ret]):
            return TrueResult()
        elif all([r == FalseResult() for r in ret]):
            return FalseResult()
        else:
            return MaybeResult()

    @normalize_types
    def SLE(self, o):
        """
        Signed less than or equal to

        :param o: The other operand
        :return: TrueResult(), FalseResult(), or MaybeResult()
        """

        signed_bounds_1 = self._signed_bounds()
        signed_bounds_2 = o._signed_bounds()

        ret = []
        for lb_1, ub_1 in signed_bounds_1:
            for lb_2, ub_2 in signed_bounds_2:
                if ub_1 <= lb_2:
                    ret.append(TrueResult())
                elif lb_1 > ub_2:
                    ret.append(FalseResult())
                else:
                    ret.append(MaybeResult())

        if all([r == TrueResult() for r in ret]):
            return TrueResult()
        elif all([r == FalseResult() for r in ret]):
            return FalseResult()
        else:
            return MaybeResult()

    @normalize_types
    def SGT(self, o):
        """
        Signed greater than
        :param o: The other operand
        :return: TrueResult(), FalseResult(), or MaybeResult()
        """

        signed_bounds_1 = self._signed_bounds()
        signed_bounds_2 = o._signed_bounds()

        ret = []
        for lb_1, ub_1 in signed_bounds_1:
            for lb_2, ub_2 in signed_bounds_2:
                if lb_1 > ub_2:
                    ret.append(TrueResult())
                elif ub_1 <= lb_2:
                    ret.append(FalseResult())
                else:
                    ret.append(MaybeResult())

        if all([r == TrueResult() for r in ret]):
            return TrueResult()
        elif all([r == FalseResult() for r in ret]):
            return FalseResult()
        else:
            return MaybeResult()

    @normalize_types
    def SGE(self, o):
        """
        Signed greater than or equal to
        :param o: The other operand
        :return: TrueResult(), FalseResult(), or MaybeResult()
        """

        signed_bounds_1 = self._signed_bounds()
        signed_bounds_2 = o._signed_bounds()

        ret = []
        for lb_1, ub_1 in signed_bounds_1:
            for lb_2, ub_2 in signed_bounds_2:
                if lb_1 >= ub_2:
                    ret.append(TrueResult())
                elif ub_1 < lb_2:
                    ret.append(FalseResult())
                else:
                    ret.append(MaybeResult())

        if all([r == TrueResult() for r in ret]):
            return TrueResult()
        elif all([r == FalseResult() for r in ret]):
            return FalseResult()
        else:
            return MaybeResult()

    @normalize_types
    def ULT(self, o):
        """
        Unsigned less than

        :param o: The other operand
        :return: TrueResult(), FalseResult(), or MaybeResult()
        """

        unsigned_bounds_1 = self._unsigned_bounds()
        unsigned_bounds_2 = o._unsigned_bounds()

        ret = []
        for lb_1, ub_1 in unsigned_bounds_1:
            for lb_2, ub_2 in unsigned_bounds_2:
                if ub_1 < lb_2:
                    ret.append(TrueResult())
                elif lb_1 >= ub_2:
                    ret.append(FalseResult())
                else:
                    ret.append(MaybeResult())

        if all([r == TrueResult() for r in ret]):
            return TrueResult()
        elif all([r == FalseResult() for r in ret]):
            return FalseResult()
        else:
            return MaybeResult()

    @normalize_types
    def ULE(self, o):
        """
        Unsigned less than or equal to

        :param o: The other operand
        :return: TrueResult(), FalseResult(), or MaybeResult()
        """

        unsigned_bounds_1 = self._unsigned_bounds()
        unsigned_bounds_2 = o._unsigned_bounds()

        ret = []
        for lb_1, ub_1 in unsigned_bounds_1:
            for lb_2, ub_2 in unsigned_bounds_2:
                if ub_1 <= lb_2:
                    ret.append(TrueResult())
                elif lb_1 > ub_2:
                    ret.append(FalseResult())
                else:
                    ret.append(MaybeResult())

        if all([r == TrueResult() for r in ret]):
            return TrueResult()
        elif all([r == FalseResult() for r in ret]):
            return FalseResult()
        else:
            return MaybeResult()

    @normalize_types
    def UGT(self, o):
        """
        Signed greater than
        :param o: The other operand
        :return: TrueResult(), FalseResult(), or MaybeResult()
        """

        unsigned_bounds_1 = self._unsigned_bounds()
        unsigned_bounds_2 = o._unsigned_bounds()

        ret = []
        for lb_1, ub_1 in unsigned_bounds_1:
            for lb_2, ub_2 in unsigned_bounds_2:
                if lb_1 > ub_2:
                    ret.append(TrueResult())
                elif ub_1 <= lb_2:
                    ret.append(FalseResult())
                else:
                    ret.append(MaybeResult())

        if all([r == TrueResult() for r in ret]):
            return TrueResult()
        elif all([r == FalseResult() for r in ret]):
            return FalseResult()
        else:
            return MaybeResult()

    @normalize_types
    def UGE(self, o):
        """
        Unsigned greater than or equal to
        :param o: The other operand
        :return: TrueResult(), FalseResult(), or MaybeResult()
        """

        unsigned_bounds_1 = self._unsigned_bounds()
        unsigned_bounds_2 = o._unsigned_bounds()

        ret = []
        for lb_1, ub_1 in unsigned_bounds_1:
            for lb_2, ub_2 in unsigned_bounds_2:
                if lb_1 >= ub_2:
                    ret.append(TrueResult())
                elif ub_1 < lb_2:
                    ret.append(FalseResult())
                else:
                    ret.append(MaybeResult())

        if all([r == TrueResult() for r in ret]):
            return TrueResult()
        elif all([r == FalseResult() for r in ret]):
            return FalseResult()
        else:
            return MaybeResult()

    def eq(self, o):
        """
        Equal

        :param o: The ohter operand
        :return: TrueResult(), FalseResult(), or MaybeResult()
        """

        if (self.is_integer
            and o.is_integer
            ):
            # Two integers
            if self.lower_bound == o.lower_bound:
                # They are equal
                return TrueResult()
            else:
                # They are not equal
                return FalseResult()

        else:
            if self.name == o.name:
                return TrueResult() # They are the same guy

            si_intersection = self.intersection(o)

            if si_intersection.is_empty:
                return FalseResult()

            else:
                return MaybeResult()

    #
    # Overriding default operators in Python
    #

    def __len__(self):
        '''
        Get the length in bits of this variable.
        :return:
        '''
        return self._bits

    @normalize_types
    def __eq__(self, o):
        return self.eq(o)

    @normalize_types
    def __ne__(self, o):
        return ~(self.eq(o))

    def __gt__(self, other):
        """
        Unsigned greater than
        :param other: The other operand
        :return: TrueResult(), FalseResult(), or MaybeResult()
        """
        return self.UGT(other)

    def __ge__(self, other):
        """
        Unsigned greater than or equal to
        :param other: The other operand
        :return: TrueResult(), FalseResult(), or MaybeResult()
        """

        return self.UGE(other)

    def __lt__(self, other):
        """
        Unsigned less than
        :param other: The other operand
        :return: TrueResult(), FalseResult(), or MaybeResult()
        """
        return self.ULT(other)

    def __le__(self, other):
        """
        Unsigned less than or equal to
        :param other: The other operand
        :return: TrueResult(), FalseResult(), or MaybeResult()
        """
        return self.ULE(other)

    @normalize_types
    def __add__(self, o):
        return self.add(o)

    @normalize_types
    def __sub__(self, o):
        return self.sub(o)

    @normalize_types
    def __mul__(self, o):
        return self.mul(o)

    @normalize_types
    def __mod__(self, o):
        # TODO: Make a better approximation
        if self.is_integer and o.is_integer:
            r = self.lower_bound % o.lower_bound
            si = StridedInterval(bits=self.bits, stride=0, lower_bound=r, upper_bound=r)
            return si

        else:
            si = StridedInterval(bits=self.bits, stride=1, lower_bound=0, upper_bound=o.upper_bound - 1)
            return si

    @normalize_types
    def __div__(self, o):
        """
        Unsigned division
        :param o: The divisor
        :return: The quotient (self / o)
        """

        return self.udiv(o)

    def __neg__(self):
        return self.bitwise_not()

    def __invert__(self):
        return self.bitwise_not()

    @expand_ifproxy
    @normalize_types
    def __or__(self, other):
        return self.bitwise_or(other)

    @normalize_types
    def __and__(self, other):
        return self.bitwise_and(other)

    def __rand__(self, other):
        return self.__and__(other)

    @expand_ifproxy
    @normalize_types
    def __xor__(self, other):
        return self.bitwise_xor(other)

    @expand_ifproxy
    def __rxor__(self, other):
        return self.__xor__(other)

    def __lshift__(self, other):
        return self.lshift(other)

    def __rshift__(self, other):
        return self.rshift(other)

    def __repr__(self):
        s = ""
        if self.is_empty:
            s = '%s<%d>[EmptySI]' % (self._name, self._bits)
        else:
            lower_bound = self._lower_bound if type(self._lower_bound) == str else '%#x' % self._lower_bound
            upper_bound = self._upper_bound if type(self._upper_bound) == str else '%#x' % self._upper_bound
            s = '%s<%d>0x%x[%s, %s]%s' % (self._name, self._bits, self._stride,
                                          lower_bound, upper_bound,
                                          'R' if self._reversed else '')

        if self.uninitialized:
            s += "(uninit)"

        return s

    #
    # Properties
    #

    @property
    def name(self):
        return self._name

    @property
    def reversed(self):
        return self._reversed

    @property
    def size(self):
        logger.warning("StridedInterval.size will be deprecated soon. Please use StridedInterval.cardinality instead.")
        return self.cardinality

    @property
    def cardinality(self):
        if self.is_integer:
            if self.is_empty:
                return 0
            else:
                return 1
        else:
            return (self._modular_sub(self._upper_bound, self._lower_bound, self.bits) + 1) / self._stride

    @property
    def lower_bound(self):
        return self._lower_bound

    @lower_bound.setter
    def lower_bound(self, value):
        self._lower_bound = value

    @property
    def upper_bound(self):
        return self._upper_bound

    @upper_bound.setter
    def upper_bound(self, value):
        self._upper_bound = value

    @property
    def bits(self):
        return self._bits

    @property
    def stride(self):
        return self._stride

    @stride.setter
    def stride(self, value):
        self._stride = value

    @property
    def max(self):
        if not self.is_empty:
            return self.upper_bound
        else:
            # It is empty!
            return None

    @property
    def min(self):
        if not self.is_empty:
            return self.lower_bound
        else:
            # It is empty
            return None

    @property
    def unique(self):
        return self.min is not None and self.min == self.max

    def _min_bits(self):
        v = self._upper_bound
        assert v >= 0
        return StridedInterval.min_bits(v)

    @property
    def is_empty(self):
        """
        The same as is_bottom
        :return: True/False
        """
        return self.is_bottom

    @property
    def is_top(self):
        '''
        If this is a TOP value
        :return: True if this is a TOP
        '''
        return (self.stride == 1 and
                self.lower_bound == self._modular_add(self.upper_bound, 1, self.bits)
                )

    @property
    def is_bottom(self):
        """
        Whether this StridedInterval is a BOTTOM, in other words, describes an empty set of integers
        :return: True/False
        """
        return self._is_bottom

    @property
    def is_integer(self):
        '''
        If this is an integer, i.e. self.lower_bound == self.upper_bound
        :return: True if this is an integer, False otherwise
        '''
        return self.lower_bound == self.upper_bound

    #
    # Modular arithmetic
    #

    @staticmethod
    def _modular_add(a, b, bits):
        return (a + b) % (2 ** bits)

    @staticmethod
    def _modular_sub(a, b, bits):
        return (a - b) % (2 ** bits)

    @staticmethod
    def _modular_mul(a, b, bits):
        return (a * b) % (2 ** bits)

    #
    # Helper methods
    #

    @staticmethod
    def lcm(a, b):
        """
        Get the least common multiple
        :param a: The first operand (integer)
        :param b: The second operand (integer)
        :return: Their LCM
        """
        return a * b // fractions.gcd(a, b)

    @staticmethod
    def highbit(k):
        return 1 << (k - 1)

    @staticmethod
    def min_bits(val):
        if val == 0:
            return 1
        elif val < 0:
            return int(math.log(-val, 2) + 1) + 1
        else:
            # Here we assume the maximum val is 64 bits
            # Special case to deal with the floating-point imprecision
            if val > 0xfffffffffffe0000 and val <= 0x10000000000000000:
                return 64
            return int(math.log(val, 2) + 1)

    @staticmethod
    def max_int(k):
        # return StridedInterval.highbit(k + 1) - 1
        return StridedInterval.highbit(k + 1) - 1

    @staticmethod
    def min_int(k):
        return -StridedInterval.highbit(k)

    @staticmethod
    def _ntz(x):
        '''
        Get the position of first non-zero bit
        :param x:
        :return:
        '''
        if x == 0:
            return 0
        y = (~x) & (x - 1)    # There is actually a bug in BAP until 0.8

        def bits(y):
            n = 0
            while y != 0:
                n += 1
                y >>= 1
            return n

        return bits(y)

    @staticmethod
    def _to_negative(a, bits):
        return -((1 << bits) - a)

    @staticmethod
    def upper(bits, i, stride):
        '''

        :return:
        '''
        if stride >= 1:
            offset = i % stride
            max = StridedInterval.max_int(bits)  # pylint:disable=redefined-builtin
            max_offset = max % stride

            if max_offset >= offset:
                o = max - (max_offset - offset)
            else:
                o = max - ((max_offset + stride) - offset)
            return o
        else:
            return StridedInterval.max_int(bits)

    @staticmethod
    def lower(bits, i, stride):
        '''

        :return:
        '''
        if stride >= 1:
            offset = i % stride
            min = StridedInterval.min_int(bits)  # pylint:disable=redefined-builtin
            min_offset = min % stride

            if offset >= min_offset:
                o = min + (offset - min_offset)
            else:
                o = min + ((offset + stride) - min_offset)
            return o
        else:
            return StridedInterval.min_int(bits)

    @staticmethod
    def top(bits, name=None, uninitialized=False):
        '''
        Get a TOP StridedInterval

        :return:
        '''
        return StridedInterval(name=name,
                               bits=bits,
                               stride=1,
                               lower_bound=0,
                               upper_bound=StridedInterval.max_int(bits),
                               uninitialized=uninitialized)

    @staticmethod
    def empty(bits):
        return StridedInterval(bits=bits, bottom=True)

    @staticmethod
    def _wrapped_cardinality(x, y, bits):
        """
        Return the cardinality for a set of number (| x, y |) on the wrapped-interval domain
        :param x: The first operand (an integer)
        :param y: The second operand (an integer)
        :return: The cardinality
        """

        if x == y + 1:
            return 2 ** bits

        else:
            return ((y - x) + 1) & (2 ** bits - 1)

    @staticmethod
    def _is_msb_zero(v, bits):
        """
        Checks if the most significant bit is zero (i.e. is the integer positive under signed arithmetic)
        :param v: The integer to check with
        :param bits: Bits of the integer
        :return: True or False
        """
        return (v & (2 ** bits - 1)) & (2 ** (bits - 1)) == 0

    @staticmethod
    def _unsigned_to_signed(v, bits):
        """
        Convert an unsigned integer to a signed integer
        :param v: The unsigned integer
        :param bits: How many bits this integer should be
        :return: The converted signed integer
        """
        if StridedInterval._is_msb_zero(v, bits):
            return v
        else:
            return -(2 ** bits - v)

    @staticmethod
    def _wrappedoverflow_add(a, b):
        """
        Determines if an overflow happens during the addition of `a` and `b`.

        :param a: The first operand (StridedInterval)
        :param b: The other operand (StridedInterval)
        :return: True if overflows, False otherwise
        """

        if a.is_integer and a.lower_bound == 0:
            # Special case: if `a` or `b` is a zero
            card_self = 0
        else:
            card_self = StridedInterval._wrapped_cardinality(a.lower_bound, a.upper_bound, a.bits)

        if b.is_integer and b.lower_bound == 0:
            # Special case: if `a` or `b` is a zero
            card_b = 0
        else:
            card_b = StridedInterval._wrapped_cardinality(b.lower_bound, b.upper_bound, b.bits)

        return (card_self + card_b) > StridedInterval.max_int(a.bits)

    @staticmethod
    def _wrappedoverflow_sub(a, b):
        """
        Determines if an overflow happens during the subtraction of `a` and `b`.

        :param a: The first operand (StridedInterval)
        :param b: The other operand (StridedInterval)
        :return: True if overflows, False otherwise
        """

        return StridedInterval._wrappedoverflow_add(a, b)

    @staticmethod
    def _wrapped_unsigned_mul(a, b):
        """
        Perform wrapped unsigned multiplication on two StridedIntervals
        :param a: The first operand (StridedInterval)
        :param b: The second operand (StridedInterval)
        :return: The multiplication result
        """

        bits = max(a.bits, b.bits)

        lb = a.lower_bound * b.lower_bound
        ub = a.upper_bound * b.upper_bound

        max_ = StridedInterval.max_int(bits)
        if lb > max_ or ub > max_:
            # Overflow occurred
            return StridedInterval.top(bits, uninitialized=False)

        else:
            if b.is_integer:
                # Multiplication with an integer, and it does not overflow!
                stride = abs(a.stride * b.lower_bound)
            elif a.is_integer:
                stride = abs(a.lower_bound * b.stride)
            else:
                stride = fractions.gcd(a.stride, b.stride)
            return StridedInterval(bits=bits, stride=stride, lower_bound=lb, upper_bound=ub)

    @staticmethod
    def _wrapped_signed_mul(a, b):
        """
        Perform wrapped signed multiplication on two StridedIntervals
        :param a: The first operand (StridedInterval)
        :param b: The second operand (StridedInterval)
        :return: The product
        """

        bits = max(a.bits, b.bits)

        a_lb_positive = StridedInterval._is_msb_zero(a.lower_bound, bits)
        a_ub_positive = StridedInterval._is_msb_zero(a.upper_bound, bits)
        b_lb_positive = StridedInterval._is_msb_zero(b.lower_bound, bits)
        b_ub_positive = StridedInterval._is_msb_zero(b.upper_bound, bits)

        if b.is_integer:
            # Multiplication with an integer, and it does not overflow!
            # Note that as long as it overflows, a TOP will be returned and the stride will be simply ignored
            stride = abs(a.stride * b.lower_bound)
        elif a.is_integer:
            stride = abs(a.lower_bound * b.stride)
        else:
            stride = fractions.gcd(a.stride, b.stride)

        max_ = StridedInterval.max_int(bits)

        if (a_lb_positive and a_ub_positive and b_lb_positive and b_ub_positive):
            # [2, 5] * [10, 20] = [20, 100]
            lb = a.lower_bound * b.lower_bound
            ub = a.upper_bound * b.upper_bound

            if lb > max_ or ub > max_:
                # overflow
                return StridedInterval.top(bits)

            else:
                return StridedInterval(bits=bits, stride=stride, lower_bound=lb, upper_bound=ub)

        elif (not a_lb_positive and not a_ub_positive and not b_lb_positive and not b_ub_positive):
            # [-5, -2] * [-20, -10] = [20, 100]
            lb = (
                StridedInterval._unsigned_to_signed(a.upper_bound, bits) *
                StridedInterval._unsigned_to_signed(b.upper_bound, bits)
            )
            ub = (
                StridedInterval._unsigned_to_signed(a.lower_bound, bits) *
                StridedInterval._unsigned_to_signed(b.lower_bound, bits)
            )

            if lb > max_ or ub > max_:
                # overflow
                return StridedInterval.top(bits)

            else:
                return StridedInterval(bits=bits, stride=stride, lower_bound=lb, upper_bound=ub)

        elif (not a_lb_positive and not a_ub_positive and b_lb_positive and b_ub_positive):
            # [-10, -2] * [2, 5] = [-50, -4]
            lb = StridedInterval._unsigned_to_signed(a.lower_bound, bits) * b.upper_bound
            ub = StridedInterval._unsigned_to_signed(a.upper_bound, bits) * b.lower_bound

            if lb & (2 ** bits - 1) > max_ or ub & (2 ** bits - 1) > max_:
                # overflow
                return StridedInterval.top(bits)

            else:
                return StridedInterval(bits=bits, stride=stride, lower_bound=lb, upper_bound=ub)

        elif (a_lb_positive and a_ub_positive and not b_lb_positive and not b_ub_positive):
            # [2, 10] * [-5, -2] = [-50, -4]
            lb = a.upper_bound * StridedInterval._unsigned_to_signed(b.lower_bound, bits)
            ub = a.lower_bound * StridedInterval._unsigned_to_signed(b.upper_bound, bits)

            if lb & (2 ** bits - 1) > max_ or ub & (2 ** bits - 1) > max_:
                # overflow
                return StridedInterval.top(bits)

            else:
                return StridedInterval(bits=bits, stride=stride, lower_bound=lb, upper_bound=ub)

        else:
            raise Exception('We shouldn\'t see this case: %s * %s' % (a, b))

    @staticmethod
    def _wrapped_unsigned_div(a, b):
        """
        Perform wrapped unsigned division on two StridedIntervals.

        :param a: The dividend (StridedInterval)
        :param b: The divisor (StridedInterval)
        :return: The quotient
        """

        bits = max(a.bits, b.bits)

        divisor_lb, divisor_ub = b.lower_bound, b.upper_bound

        # Make sure divisor_lb and divisor_ub is not 0
        if divisor_lb == 0:
            # Can we increment it?
            if divisor_ub == 0:
                # We can't :-(
                return StridedInterval.empty(bits)
            else:
                divisor_lb += 1

        lb = a.lower_bound / divisor_ub
        ub = a.upper_bound / divisor_lb

        # TODO: Can we make a more precise estimate of the stride?
        stride = 1

        return StridedInterval(bits=bits, stride=stride, lower_bound=lb, upper_bound=ub)

    @staticmethod
    def _wrapped_signed_div(a, b):
        """
        Perform wrapped unsigned division on two StridedIntervals.

        :param a: The dividend (StridedInterval)
        :param b: The divisor (StridedInterval)
        :return: The quotient
        """

        bits = max(a.bits, b.bits)

        # Make sure the divisor is not 0
        divisor_lb = b.lower_bound
        divisor_ub = b.upper_bound
        if divisor_lb == 0:
            # Try to increment it
            if divisor_ub == 0:
                return StridedInterval.empty(bits)
            else:
                divisor_lb = 1

        dividend_positive = StridedInterval._is_msb_zero(a.lower_bound, bits)
        divisor_positive = StridedInterval._is_msb_zero(b.lower_bound, bits)

        # TODO: Can we make a more precise estimate of the stride?
        stride = 1
        if dividend_positive and divisor_positive:
            # They are all positive numbers!
            lb = a.lower_bound / divisor_ub
            ub = a.upper_bound / divisor_lb

        elif dividend_positive and not divisor_positive:
            # + / -
            lb = a.upper_bound / StridedInterval._unsigned_to_signed(divisor_ub, bits)
            ub = a.lower_bound / StridedInterval._unsigned_to_signed(divisor_lb, bits)

        elif not dividend_positive and divisor_positive:
            # - / +
            lb = StridedInterval._unsigned_to_signed(a.lower_bound, bits) / divisor_lb
            ub = StridedInterval._unsigned_to_signed(a.upper_bound, bits) / divisor_ub

        else:
            # - / -
            lb = StridedInterval._unsigned_to_signed(a.upper_bound, bits) / \
                 StridedInterval._unsigned_to_signed(b.lower_bound, bits)
            ub = StridedInterval._unsigned_to_signed(a.lower_bound, bits) / \
                 StridedInterval._unsigned_to_signed(b.upper_bound, bits)

        return StridedInterval(bits=bits, stride=stride, lower_bound=lb, upper_bound=ub)

    @staticmethod
    def _wrapped_bitwise_or(a, b):
        if a.is_empty or b.is_empty:
            logger.error('Bitwise_or on empty strided-intervals.')
            return a.copy()

        # Special handling for integers
        # TODO: Is this special handling still necessary?
        if a.is_integer:
            # self is an integer
            t = StridedInterval._ntz(b.stride)
        elif b.is_integer:
            # b is an integer
            t = StridedInterval._ntz(a.stride)
        else:
            t = min(StridedInterval._ntz(a.stride), StridedInterval._ntz(b.stride))

        # If a or b is zero, we can make the stride more precise!
        premask = 1 << t
        if a.is_integer and a.lower_bound == 0:
            # a is 0
            # or'ng with zero does not change the stride
            stride_ = b.stride
        elif b.is_integer and b.lower_bound == 0:
            # b is 0
            stride_ = a.stride
        else:
            stride_ = 1 << t
        lowbits = (a.lower_bound | b.lower_bound) & (premask - 1)

        # TODO: Make this function looks better
        r_1 = a.lower_bound < 0
        r_2 = a.upper_bound < 0
        r_3 = b.lower_bound < 0
        r_4 = b.upper_bound < 0

        if (r_1, r_2, r_3, r_4) == (True, True, True, True):
            lb_ = StridedInterval.min_or(a.bits, a.lower_bound, a.upper_bound, b.lower_bound, b.upper_bound)
            ub_ = StridedInterval.max_or(a.bits, a.lower_bound, a.upper_bound, b.lower_bound, b.upper_bound)
        elif (r_1, r_2, r_3, r_4) == (True, True, False, False):
            lb_ = StridedInterval.min_or(a.bits, a.lower_bound, a.upper_bound, b.lower_bound, b.upper_bound)
            ub_ = StridedInterval.max_or(a.bits, a.lower_bound, a.upper_bound, b.lower_bound, b.upper_bound)
        elif (r_1, r_2, r_3, r_4) == (False, False, True, True):
            lb_ = StridedInterval.min_or(a.bits, a.lower_bound, a.upper_bound, b.lower_bound, b.upper_bound)
            ub_ = StridedInterval.max_or(a.bits, a.lower_bound, a.upper_bound, b.lower_bound, b.upper_bound)
        elif (r_1, r_2, r_3, r_4) == (False, False, False, False):
            lb_ = StridedInterval.min_or(a.bits, a.lower_bound, a.upper_bound, b.lower_bound, b.upper_bound)
            ub_ = StridedInterval.max_or(a.bits, a.lower_bound, a.upper_bound, b.lower_bound, b.upper_bound)
        elif (r_1, r_2, r_3, r_4) == (True, True, True, False):
            lb_ = a.lower_bound
            ub_ = 1
        elif (r_1, r_2, r_3, r_4) == (True, False, True, True):
            lb_ = b.lower_bound
            ub_ = 1
        elif (r_1, r_2, r_3, r_4) == (True, False, True, False):
            lb_ = min(a.lower_bound, b.lower_bound)
            ub_ = StridedInterval.max_or(a.bits, 0, a.upper_bound, 0, b.upper_bound)
        elif (r_1, r_2, r_3, r_4) == (True, False, False, False):
            lb_ = StridedInterval.min_or(a.bits, a.lower_bound, 1, b.lower_bound, b.upper_bound)
            ub_ = StridedInterval.max_or(a.bits, 0, a.upper_bound, b.lower_bound, b.upper_bound)
        elif (r_1, r_2, r_3, r_4) == (False, False, True, False):
            lb_ = StridedInterval.min_or(a.bits, a.lower_bound, a.upper_bound, b.lower_bound, 1)
            ub_ = StridedInterval.max_or(a.bits, a.lower_bound, a.upper_bound, b.lower_bound, b.upper_bound)
        else:
            raise ArithmeticError("Impossible")

        highmask = ~(premask - 1)
        ret = StridedInterval(bits=a.bits, stride=stride_, lower_bound=(lb_ & highmask) | lowbits,
                              upper_bound=(ub_ & highmask) | lowbits)
        ret.normalize()

        return ret

    @staticmethod
    def _wrapped_bitwise_and(a, b):
        def number_of_ones(n):
            ctr = 0
            while n > 0:
                ctr += 1
                n &= n - 1

            return ctr

        # If only one bit is set in b, we can make it more precise
        if b.is_integer:
            if b.lower_bound == (1 << (b.bits - 1)):
                # It's testing the sign bit
                stride = 1 << (b.bits - 1)
                if a.lower_bound < 0:
                    if a.upper_bound >= 0:
                        return StridedInterval(bits=b.bits, stride=stride, lower_bound=0, upper_bound=stride)
                    else:
                        return StridedInterval(bits=b.bits, stride=0, lower_bound=stride, upper_bound=stride)
                else:
                    if a.lower_bound >= stride and a.upper_bound >= stride:
                        return StridedInterval(bits=b.bits, stride=0, lower_bound=stride, upper_bound=stride)
                    elif a.lower_bound < stride and a.upper_bound >= stride:
                        return StridedInterval(bits=b.bits, stride=stride, lower_bound=0, upper_bound=stride)
                    else:
                        return StridedInterval(bits=b.bits, stride=0, lower_bound=0, upper_bound=0)

            elif number_of_ones(b.lower_bound) == 1:
                if a.lower_bound < 0 and a.upper_bound > 0:
                    mask = (2 ** a.bits) - 1
                    s = a.copy()
                    s.lower_bound = a.lower_bound & mask
                    if s.lower_bound > s.upper_bound:
                        t = s.upper_bound
                        s.upper_bound = s.lower_bound
                        s.lower_bound = t

                else:
                    s = a

                first_one_pos = StridedInterval._ntz(b.lower_bound)

                stride = 2 ** first_one_pos
                if s.lower_bound <= stride and s.upper_bound >= stride:
                    return StridedInterval(bits=s.bits, stride=stride, lower_bound=0, upper_bound=stride)
                elif s.upper_bound < stride:
                    return StridedInterval(bits=s.bits, stride=0, lower_bound=0, upper_bound=0)
                else:
                    return StridedInterval(bits=s.bits, stride=0, lower_bound=stride, upper_bound=stride)

        return a.bitwise_not().bitwise_or(b.bitwise_not()).bitwise_not()

    #
    # Membership testing and poset ordering
    #

    @staticmethod
    def _lex_lte(x, y, bits):
        """
        Lexicographical LTE comparison

        :param x: The first operand (integer)
        :param y: The second operand (integer)
        :param bits: bit-width of the operands
        :return: True or False
        """

        return (x & (2 ** bits - 1)) <= (y & (2 ** bits - 1))

    @staticmethod
    def _lex_lt(x, y, bits):
        """
        Lexicographical LT comparison

        :param x: The first operand (integer)
        :param y: The second operand (integer)
        :param bits: bit-width of the operands
        :return: True or False
        """

        return (x & (2 ** bits - 1)) < (y & (2 ** bits - 1))

    def _wrapped_member(self, v):
        """
        Test if integer v belongs to StridedInterval a

        :param self: A StridedInterval instance
        :param v: An integer
        :return: True or False
        """

        a = self
        return self._lex_lte(v - a.lower_bound, a.upper_bound - a.lower_bound, a.bits)

    def _wrapped_lte(self, b):
        """
        Perform a wrapped LTE comparison based on the poset ordering

        :param a: The first operand
        :param b: The second operand
        :return: True if a <= b, False otherwise
        """

        a = self
        if a.is_empty:
            return True

        if a.is_top and b.is_top:
            return True

        elif a.is_top:
            return False

        elif b.is_top:
            return True

        if b._wrapped_member(a.lower_bound) and b._wrapped_member(a.upper_bound):
            if ((b.lower_bound == a.lower_bound and b.upper_bound == a.upper_bound)
                    or not a._wrapped_member(b.lower_bound) or not a._wrapped_member(b.upper_bound)):
                return True
        return False

    #
    # Arithmetic operations
    #

    def neg(self):
        """
        Unary operation: neg

        :return: 0 - self
        """

        return StridedInterval(bits=self.bits, stride=0, lower_bound=0, upper_bound=0).sub(self)

    def add(self, b):
        """
        Binary operation: add

        :param b: The other operand
        :return: self + b
        """
        new_bits = max(self.bits, b.bits)

        # TODO: Some improvements can be made here regarding the following case
        # TODO: SI<16>0xff[0x0, 0xff] + 3
        # TODO: In current implementation, it overflows, but it doesn't have to

        overflow = self._wrappedoverflow_add(self, b)
        if overflow:
            return StridedInterval.top(self.bits)

        lb = self._modular_add(self.lower_bound, b.lower_bound, new_bits)
        ub = self._modular_add(self.upper_bound, b.upper_bound, new_bits)

        # Is it initialized?
        uninitialized = self.uninitialized or b.uninitialized

        # Take the GCD of two operands' strides
        stride = fractions.gcd(self.stride, b.stride)

        return StridedInterval(bits=new_bits, stride=stride, lower_bound=lb, upper_bound=ub,
                               uninitialized=uninitialized)

    def sub(self, b):
        """
        Binary operation: sub

        :param b: The other operand
        :return: self - b
        """

        new_bits = max(self.bits, b.bits)

        overflow = self._wrappedoverflow_sub(self, b)
        if overflow:
            return StridedInterval.top(self.bits)

        lb = self._modular_sub(self.lower_bound, b.upper_bound, new_bits)
        ub = self._modular_sub(self.upper_bound, b.lower_bound, new_bits)

        # Is it initialized?
        uninitialized = self.uninitialized or b.uninitialized

        # Take the GCD of two operands' strides
        stride = fractions.gcd(self.stride, b.stride)

        return StridedInterval(bits=new_bits, stride=stride, lower_bound=lb, upper_bound=ub,
                               uninitialized=uninitialized)

    def mul(self, o):
        """
        Binary operation: multiplication

        :param o: The other operand
        :return: self * o
        """

        if self.is_integer and o.is_integer:
            # Two integers!
            a, b = self.lower_bound, o.lower_bound
            ret = StridedInterval(bits=self.bits,
                                  stride=0,
                                  lower_bound=a * b,
                                  upper_bound=a * b
                                  )

            return ret.normalize()

        else:
            # All other cases

            # Cut from both north pole and south pole
            si1_psplit = self._psplit()
            si2_psplit = o._psplit()

            ret = None
            for si1 in si1_psplit:
                for si2 in si2_psplit:
                    tmp_unsigned_mul = self._wrapped_unsigned_mul(si1, si2)
                    tmp_signed_mul = self._wrapped_signed_mul(si1, si2)

                    tmp_meet = tmp_unsigned_mul.intersection(tmp_signed_mul)

                    if ret is None:
                        ret = tmp_meet
                    else:
                        ret = ret.union(tmp_meet)

        return ret.normalize()

    def sdiv(self, o):
        """
        Binary operation: signed division

        :param o: The divisor
        :return: (self / o) in signed arithmetic
        """

        splitted_dividends = self._nsplit()
        splitted_divisors = o._nsplit()

        ret = self.empty(self.bits)
        for dividend in splitted_dividends:
            for divisor in splitted_divisors:
                tmp = self._wrapped_signed_div(dividend, divisor)
                ret = ret.union(tmp)

        return ret.normalize()

    def udiv(self, o):
        """
        Binary operation: unsigned division

        :param o: The divisor
        :return: (self / o) in unsigned arithmetic
        """

        splitted_dividends = self._ssplit()
        splitted_divisors = o._ssplit()

        ret = self.empty(self.bits)
        for dividend in splitted_dividends:
            for divisor in splitted_divisors:
                tmp = self._wrapped_unsigned_div(dividend, divisor)
                ret = ret.union(tmp)

        return ret.normalize()

    def bitwise_not(self):
        """
        Unary operation: bitwise not

        :return: ~self
        """
        splitted_si = self._ssplit()

        ret = StridedInterval.empty(self.bits)

        for si in splitted_si:
            lb = ~self.upper_bound
            ub = ~self.lower_bound
            stride = self.stride

            tmp = StridedInterval(bits=self.bits, stride=stride, lower_bound=lb, upper_bound=ub)
            ret = ret.union(tmp)

        return ret

    @staticmethod
    def min_or(k, a, b, c, d):
        m = StridedInterval.highbit(k)
        ret = 0
        while True:
            if m == 0:
                ret = a | c
                break
            elif (~a & c & m) != 0:
                tmp = (a | m) & -m
                if tmp <= b:
                    ret = tmp | c
                    break
            elif (a & ~c & m) != 0:
                tmp = (c | m) & -m
                if tmp <= d:
                    ret = tmp | a
                    break
            m = m >> 1

        return ret

    @staticmethod
    def max_or(k, a, b, c, d):
        m = StridedInterval.highbit(k)
        while True:
            if m == 0:
                return b | d
            elif (b & d & m) != 0:
                tmp1 = (b - m) | (m - 1)
                tmp2 = (d - m) | (m - 1)
                if tmp1 >= a:
                    return tmp1 | d
                elif tmp2 >= c:
                    return tmp2 | b
            m = m >> 1

    def bitwise_or(self, b):
        """
        Binary operation: logical or
        :param b: The other operand
        :return: self | b
        """

        splitted_a = self._ssplit()
        splitted_b = b._ssplit()

        ret = StridedInterval.empty(self.bits)
        for x in splitted_a:
            for y in splitted_b:
                tmp = self._wrapped_bitwise_or(x, y)
                ret = ret.union(tmp)

        return ret.normalize()

    def bitwise_and(self, b):
        """
        Binary operation: logical and
        :param b: The other operand
        :return:
        """

        splitted_a = self._ssplit()
        splitted_b = b._ssplit()

        ret = StridedInterval.empty(self.bits)
        for x in splitted_a:
            for y in splitted_b:
                tmp = self._wrapped_bitwise_and(x, y)
                ret = ret.union(tmp)

        return ret.normalize()

    def bitwise_xor(self, b):
        '''
        Operation xor
        :param b: The other operand
        :return:
        '''
        return self.bitwise_not().bitwise_or(b).bitwise_not().bitwise_or(b.bitwise_not().bitwise_or(self).bitwise_not())

    def _pre_shift(self, shift_amount):
        def get_range(expr):
            '''
            Get the range of bits for shifting
            :param expr:
            :return: A tuple of maximum and minimum bits to shift
            '''
            def round(max, x): #pylint:disable=redefined-builtin
                if x < 0 or x > max:
                    return max
                else:
                    return x

            if type(expr) in [int, long]:
                return (expr, expr)

            assert type(expr) is StridedInterval

            if expr.is_integer:
                return (round(self.bits, expr.lower_bound),
                        round(self.bits, expr.lower_bound))
            else:
                if expr.lower_bound < 0:
                    if expr.upper_bound >= 0:
                        return (0, self.bits)
                    else:
                        return (self.bits, self.bits)
                else:
                    return (round(self.bits, self.lower_bound), round(self.bits, self.upper_bound))

        lower, upper = get_range(shift_amount)
        # TODO: Is trancating necessary?

        return lower, upper

    def rshift(self, shift_amount):
        lower, upper = self._pre_shift(shift_amount)

        # Shift the lower_bound and upper_bound by all possible amounts, and
        # get min/max values from all the resulting values

        new_lower_bound = None
        new_upper_bound = None
        for shift_amount in xrange(lower, upper + 1):
            l = self.lower_bound >> shift_amount
            if new_lower_bound is None or l < new_lower_bound:
                new_lower_bound = l
            u = self.upper_bound >> shift_amount
            if new_upper_bound is None or u > new_upper_bound:
                new_upper_bound = u

        # NOTE: If this is an arithmetic operation, we should take care
        # of sign-changes.

        ret = StridedInterval(bits=self.bits,
                               stride=max(self.stride >> upper, 1),
                               lower_bound=new_lower_bound,
                               upper_bound=new_upper_bound)
        ret.normalize()

        return ret

    def lshift(self, shift_amount):
        lower, upper = self._pre_shift(shift_amount)

        # Shift the lower_bound and upper_bound by all possible amounts, and
        # get min/max values from all the resulting values

        new_lower_bound = None
        new_upper_bound = None
        for shift_amount in xrange(lower, upper + 1):
            l = self.lower_bound << shift_amount
            if new_lower_bound is None or l < new_lower_bound:
                new_lower_bound = l
            u = self.upper_bound << shift_amount
            if new_upper_bound is None or u > new_upper_bound:
                new_upper_bound = u

        # NOTE: If this is an arithmetic operation, we should take care
        # of sign-changes.

        ret = StridedInterval(bits=self.bits,
                               stride=max(self.stride << lower, 1),
                               lower_bound=new_lower_bound,
                               upper_bound=new_upper_bound)
        ret.normalize()

        return ret

    def cast_low(self, tok):
        assert tok <= self.bits

        if tok == self.bits:
            return self.copy()
        else:
            # Calcualte the new upper bound and lower bound
            mask = (1 << tok) - 1
            if (self.lower_bound & mask) == self.lower_bound and \
                (self.upper_bound & mask) == self.upper_bound:
                return StridedInterval(bits=tok, stride=self.stride,
                                       lower_bound=self.lower_bound,
                                       upper_bound=self.upper_bound)

            elif self.upper_bound - self.lower_bound <= mask:
                l = self.lower_bound & mask
                u = self.upper_bound & mask
                # Keep the signs!
                if self.lower_bound < 0:
                    l = StridedInterval._to_negative(l, tok)
                if self.upper_bound < 0:
                    u = StridedInterval._to_negative(u, tok)
                return StridedInterval(bits=tok, stride=self.stride,
                                       lower_bound=l,
                                       upper_bound=u)

            elif (self.upper_bound & mask == self.lower_bound & mask) and \
                ((self.upper_bound - self.lower_bound) & mask == 0):
                # This operation doesn't affect the stride. Stride should be 0 then.

                bound = self.lower_bound & mask

                return StridedInterval(bits=tok,
                                       stride=0,
                                       lower_bound=bound,
                                       upper_bound=bound)

            else:
                # TODO: How can we do better here? For example, keep the stride information?
                return self.top(tok)

    @normalize_types
    def concat(self, b):
        # Zero-extend
        a = self.nameless_copy()
        a._bits += b.bits

        new_si = a.lshift(b.bits)
        new_b = b.copy()
        # Zero-extend b
        new_b._bits = new_si.bits

        if new_si.is_integer:
            # We can be more precise!
            new_si._bits = new_b.bits
            new_si._stride = new_b.stride
            new_si._lower_bound = new_si.lower_bound + b.lower_bound
            new_si._upper_bound = new_si.upper_bound + b.upper_bound
            return new_si
        else:
            return new_si.bitwise_or(new_b)

    def extract(self, high_bit, low_bit):

        if self._reversed:
            reversed = self._reverse()
            return reversed.extract(high_bit, low_bit)

        assert low_bit >= 0

        bits = high_bit - low_bit + 1

        if low_bit != 0:
            ret = self.rshift(low_bit)
        else:
            ret = self.copy()
        if bits != self.bits:
            ret = ret.cast_low(bits)

        return ret.normalize()

    def sign_extend(self, new_length):
        """
        Unary operation: SignExtend

        :param new_length: New length after sign-extension
        :return: A new StridedInterval
        """

        msb = self.extract(self.bits - 1, self.bits - 1).eval(2)

        if msb == [ 0 ]:
            # All positive numbers
            return self.zero_extend(new_length)

        if msb == [ 1 ]:
            # All negative numbers

            si = self.copy()
            si._bits = new_length

            mask = (2 ** new_length - 1) - (2 ** self.bits - 1)
            si._lower_bound = si._lower_bound | mask
            si._upper_bound = si._upper_bound | mask

        else:
            # Both positive numbers and negative numbers
            numbers = self._nsplit()

            # Since there are both positive and negative numbers, there must be two bounds after nsplit
            # assert len(numbers) == 2

            si = self.empty(new_length)

            for n in numbers:
                a, b = n.lower_bound, n.upper_bound

                if b < 2 ** (n.bits - 1):
                    # msb = 0

                    si_ = StridedInterval(bits=new_length, stride=n.stride, lower_bound=a, upper_bound=b)

                else:
                    # msb = 1

                    mask = (2 ** new_length - 1) - (2 ** self.bits - 1)

                    si_ = StridedInterval(bits=new_length, stride=n.stride, lower_bound=a | mask, upper_bound=b | mask)

                si = si.union(si_)

        return si

    def zero_extend(self, new_length):
        """
        Unary operation: ZeroExtend

        :param new_length: New length after zero-extension
        :return: A new StridedInterval
        """

        si = self.copy()
        si._bits = new_length

        return si

    @normalize_types
    def union(self, b):
        """
        The union operation. It might return a DiscreteStridedIntervalSet to allow for better precision in analysis.

        :param b: Operand
        :return: A new DiscreteStridedIntervalSet, or a new StridedInterval.
        """
        if not allow_dsis:
            return self._union(b)

        else:
            if self.cardinality > discrete_strided_interval_set.MAX_CARDINALITY_WITHOUT_COLLAPSING or \
                    b.cardinality > discrete_strided_interval_set:
                return self._union(b)

            else:
                dsis = DiscreteStridedIntervalSet(bits=self._bits, si_set={ self })
                return dsis.union(b)

    @normalize_types
    def _union(self, b):
        """
        Binary operation: union
        It's also the join operation.

        :param b: The other operand.
        :return: A new StridedInterval
        """
        if self._reversed != b._reversed:
            logger.warning('Incoherent reversed flag between operands %s and %s', self, b)

        #
        # Trivial cases
        #

        if self.is_empty:
            return b
        if b.is_empty:
            return self

        if self.is_integer and b.is_integer:
            u = max(self.upper_bound, b.upper_bound)
            l = min(self.lower_bound, b.lower_bound)
            stride = abs(u - l)
            return StridedInterval(bits=self.bits, stride=stride, lower_bound=l, upper_bound=u)

        #
        # Other cases
        #

        # Determine the new stride
        if self.is_integer:
            new_stride = fractions.gcd(self._modular_sub(self.lower_bound, b.lower_bound, self.bits), b.stride)
        elif b.is_integer:
            new_stride = fractions.gcd(self.stride, self._modular_sub(b.lower_bound, self.lower_bound, self.bits))
        else:
            new_stride = fractions.gcd(self.stride, b.stride)

        remainder_1 = self.lower_bound % new_stride if new_stride > 0 else 0
        remainder_2 = b.lower_bound % new_stride if new_stride > 0 else 0
        if remainder_1 != remainder_2:
            new_stride = fractions.gcd(abs(remainder_1 - remainder_2), new_stride)

        # Then we have different cases

        if self._wrapped_lte(b):
            # Containment

            return StridedInterval(bits=self.bits, stride=new_stride, lower_bound=b.lower_bound,
                                   upper_bound=b.upper_bound)

        elif b._wrapped_lte(self):
            # Containment

            # TODO: This case is missing in the original implementation. Is that a bug?
            return StridedInterval(bits=self.bits, stride=new_stride, lower_bound=self.lower_bound,
                                   upper_bound=self.upper_bound)

        elif (self._wrapped_member(b.lower_bound) and self._wrapped_member(b.upper_bound) and
            b._wrapped_member(self.lower_bound) and b._wrapped_member(self.upper_bound)):
            # The union of them covers the entire sphere

            return StridedInterval.top(self.bits)

        elif self._wrapped_member(b.lower_bound):
            # Overlapping

            return StridedInterval(bits=self.bits, stride=new_stride, lower_bound=self.lower_bound,
                                   upper_bound=b.upper_bound)

        elif b._wrapped_member(self.lower_bound):
            # Overlapping

            return StridedInterval(bits=self.bits, stride=new_stride, lower_bound=b.lower_bound,
                                   upper_bound=self.upper_bound)

        else:
            card_1 = self._wrapped_cardinality(self.upper_bound, b.lower_bound, self.bits)
            card_2 = self._wrapped_cardinality(b.upper_bound, self.lower_bound, self.bits)

            if card_1 == card_2:
                # Left/right leaning cases
                if self._lex_lt(self.lower_bound, b.lower_bound, self.bits):
                    return StridedInterval(bits=self.bits, stride=new_stride, lower_bound=self.lower_bound,
                                           upper_bound=b.upper_bound)

                else:
                    return StridedInterval(bits=self.bits, stride=new_stride, lower_bound=b.lower_bound,
                                           upper_bound=self.upper_bound)

            elif card_1 < card_2:
                # non-overlapping case (left)
                return StridedInterval(bits=self.bits, stride=new_stride, lower_bound=self.lower_bound,
                                       upper_bound=b.upper_bound)

            else:
                # non-overlapping case (right)
                return StridedInterval(bits=self.bits, stride=new_stride, lower_bound=b.lower_bound,
                                       upper_bound=self.upper_bound)

    def _minimum_intersection_integer(self, other, lb_from_self):
        """
        Solves for the minimum integer that exists in both StridedIntervals

        :param other: The other operand
        :param lb_from_self: True/False. If True, then we have `other` contains `self` or `other` contains
                            `self`.lower_bound, and vice versa
        :return: The minimum integer if there is one, or None if it doesn't exist.
        """

        # It's equivalent to find a integral solution for equation `ax + b = cy + d` that makes `ax + b` minimal
        # Some assumptions:
        # a, b, c, d are all positive integers
        # x >= 0, y >= 0

        a, b, c, d = self.stride, self.lower_bound, other.stride, other.lower_bound

        if (d - b) % self.lcm(a, c) != 0:
            # They don't overlap
            return None

        if c % a:
            p = c / a

            if not lb_from_self:
                k1 = (d - b) / a # It must be an integer
                k = int(k1 + 0.5)
            else:
                k2 = (b - d) * (c * 1.0 / a - p) / c + (d - b) / a
                k = int(k2 + 0.5)

            y = (k - (d - b) / a) / (c * 1.0 / a - p)
            first_integer = int(c * y + d)

        else:
            if lb_from_self:
                first_integer = b
            else:
                first_integer = d

        if self._wrapped_member(first_integer) and \
                self._modular_sub(first_integer, self.lower_bound, self.bits) % self.stride == 0 and \
                other._wrapped_member(first_integer) and \
                other._modular_sub(first_integer, other.lower_bound, other.bits) % other.stride == 0:
            return first_integer
        else:
            return None

    @normalize_types
    def intersection(self, b):
        if self.is_empty or b.is_empty:
            return StridedInterval.empty(self.bits)

        assert self.bits == b.bits

        if self.is_integer and b.is_integer:
            if self.lower_bound == b.lower_bound:
                # They are the same number!
                ret = StridedInterval(bits=self.bits,
                                      stride=0,
                                      lower_bound=self.lower_bound,
                                      upper_bound=self.lower_bound)
            else:
                ret = StridedInterval.empty(self.bits)

        elif self.is_integer:
            integer = self.lower_bound
            if (b.lower_bound - integer) % b.stride == 0 and \
                    b._wrapped_member(integer):
                ret = StridedInterval(bits=self.bits,
                                      stride=0,
                                      lower_bound=integer,
                                      upper_bound=integer)
            else:
                ret = StridedInterval.empty(self.bits)

        elif b.is_integer:
            integer = b.lower_bound
            if (integer - self.lower_bound) % self.stride == 0 and \
                    self._wrapped_member(integer):
                ret = StridedInterval(bits=self.bits,
                                      stride=0,
                                      lower_bound=integer,
                                      upper_bound=integer)
            else:
                ret = StridedInterval.empty(self.bits)

        else:
            # None of the operands is an integer

            new_stride = self.lcm(self.stride, b.stride)
            if self._wrapped_lte(b):
                # `b` may fully contain `self`

                lb = self._minimum_intersection_integer(b, True)
                if lb is None:
                    ret = StridedInterval.empty(self.bits)

                else:
                    ub = self._modular_add(
                        self._modular_sub(self.upper_bound, lb, self.bits) / new_stride * new_stride,
                        lb,
                        self.bits
                    )
                    ret = StridedInterval(bits=self.bits,
                                           stride=new_stride,
                                           lower_bound=lb,
                                           upper_bound=ub
                                           )

            elif b._wrapped_lte(self):
                # `self` contains `b`

                lb = b._minimum_intersection_integer(self, True)

                if lb is None:
                    ret = StridedInterval.empty(self.bits)

                else:
                    ub = self._modular_add(
                        self._modular_sub(b.upper_bound, lb, self.bits) / new_stride * new_stride,
                        lb,
                        self.bits
                    )
                    ret = StridedInterval(bits=self.bits,
                                           stride=new_stride,
                                           lower_bound=lb,
                                           upper_bound=ub
                                           )

            elif self._wrapped_member(b.lower_bound) and \
                    self._wrapped_member(b.upper_bound) and \
                    b._wrapped_member(self.lower_bound) and \
                    b._wrapped_member(self.upper_bound):
                # One cover the other

                card_1 = self._wrapped_cardinality(self.lower_bound, self.upper_bound, self.bits)
                card_2 = self._wrapped_cardinality(b.lower_bound, b.upper_bound, b.bits)
                if self._lex_lt(card_1, card_2, self.bits) or \
                        (card_1 == card_2 and self._lex_lte(self.lower_bound, b.lower_bound, self.bits)):
                    lb = self._minimum_intersection_integer(b, True)

                    if lb is None:
                        ret = StridedInterval.empty(self.bits)

                    else:
                        ub = self._modular_add(
                            self._modular_sub(self.upper_bound, lb, self.bits) / new_stride * new_stride,
                            lb,
                            self.bits
                        )
                        ret = StridedInterval(bits=self.bits,
                                               stride=new_stride,
                                               lower_bound=lb,
                                               upper_bound=ub
                                               )
                else:
                    lb = self._minimum_intersection_integer(b, False)

                    if lb is None:
                        ret = StridedInterval.empty(self.bits)

                    else:
                        ub = self._modular_add(
                            self._modular_sub(b.upper_bound, lb, self.bits) / new_stride * new_stride,
                            lb,
                            self.bits
                        )
                        ret = StridedInterval(bits=self.bits,
                                               stride=new_stride,
                                               lower_bound=lb,
                                               upper_bound=ub
                                               )
            elif self._wrapped_member(b.lower_bound):
                # Overlapping

                lb = b._minimum_intersection_integer(self, True)

                if lb is None:
                    ret = StridedInterval.empty(self.bits)

                else:
                    ub = self._modular_add(
                        self._modular_sub(self.upper_bound, lb, self.bits) / new_stride * new_stride,
                        lb,
                        self.bits
                    )
                    ret = StridedInterval(bits=self.bits,
                                           stride=new_stride,
                                           lower_bound=lb,
                                           upper_bound=ub
                                           )

            elif b._wrapped_member(self.lower_bound):
                # Overlapping

                lb = self._minimum_intersection_integer(b, True)

                if lb is None:
                    ret = StridedInterval.empty(self.bits)

                else:
                    ub = self._modular_add(
                        self._modular_sub(b.upper_bound, lb, self.bits) / new_stride * new_stride,
                        lb,
                        self.bits
                    )
                    ret = StridedInterval(bits=self.bits,
                                           stride=new_stride,
                                           lower_bound=lb,
                                           upper_bound=ub
                                           )

            else:
                # Disjoint
                ret = StridedInterval.empty(self.bits)

        ret.normalize()
        return ret

    @normalize_types
    def widen(self, b):
        ret = None

        if self.is_empty and not b.is_empty:
            ret = StridedInterval.top(bits=self.bits)

        elif self.is_empty:
            ret = b

        elif b.is_empty:
            ret = self

        else:
            new_stride = fractions.gcd(self.stride, b.stride)
            l = StridedInterval.lower(self.bits, self.lower_bound, new_stride) + 2 if b.lower_bound < self.lower_bound else self.lower_bound
            u = StridedInterval.upper(self.bits, self.upper_bound, new_stride) - 2 if b.upper_bound > self.upper_bound else self.upper_bound
            if new_stride == 0:
                if self.is_integer and b.is_integer:
                    ret = StridedInterval(bits=self.bits, stride=u - l, lower_bound=l, upper_bound=u)
                else:
                    raise ClaripyOperationError('SI: operands are not reduced.')
            else:
                ret = StridedInterval(bits=self.bits, stride=new_stride, lower_bound=l, upper_bound=u)

        ret.normalize()
        return ret

    def reverse(self):
        if self.bits == 8:
            # We cannot reverse a one-byte value
            return self.copy()

        si = self.copy()
        si._reversed = not si._reversed

        return si

    def _reverse(self):
        """
        This function does the reversing for real.
        :return: A new reversed StridedInterval instance
        """

        o = self.copy()
        # Clear the reversed flag
        o._reversed = not o._reversed

        if o.bits == 8:
            # No need for reversing
            return o.copy()

        if o.is_top:
            # A TOP is still a TOP after reversing
            si = o.copy()
            return si

        else:
            if not o.is_integer:
                # We really don't want to do that... but well, sometimes it just happens...
                logger.warning('Reversing a real strided-interval %s is bad', self)

            # Reversing an integer is easy
            rounded_bits = ((o.bits + 7) / 8) * 8
            list_bytes = [ ]
            si = None

            for i in xrange(0, rounded_bits, 8):
                b = o.extract(min(i + 7, o.bits - 1), i)
                list_bytes.append(b)

            for b in list_bytes:
                si = b if si is None else si.concat(b)

            return si

def CreateStridedInterval(name=None, bits=0, stride=None, lower_bound=None, upper_bound=None, to_conv=None):
    '''
    :param name:
    :param bits:
    :param stride:
    :param lower_bound:
    :param upper_bound:
    :param to_conv:
    :return:
    '''
    if to_conv is not None:
        if isinstance(to_conv, Base):
            to_conv = to_conv.model
        if isinstance(to_conv, StridedInterval):
            # No conversion will be done
            return to_conv

        if type(to_conv) not in {int, long, BVV}: #pylint:disable=unidiomatic-typecheck
            raise ClaripyOperationError('Unsupported to_conv type %s' % type(to_conv))

        if stride is not None or lower_bound is not None or \
                        upper_bound is not None:
            raise ClaripyOperationError('You cannot specify both to_conv and other parameters at the same time.')

        if type(to_conv) is BVV: #pylint:disable=unidiomatic-typecheck
            bits = to_conv.bits
            to_conv_value = to_conv.value
        else:
            bits = bits
            to_conv_value = to_conv

        stride = 0
        lower_bound = to_conv_value
        upper_bound = to_conv_value

    bi = StridedInterval(name=name,
                         bits=bits,
                         stride=stride,
                         lower_bound=lower_bound,
                         upper_bound=upper_bound)
    return bi


from .errors import ClaripyVSAError
from ..errors import ClaripyOperationError
from .bool_result import TrueResult, FalseResult, MaybeResult
from . import discrete_strided_interval_set
from .discrete_strided_interval_set import DiscreteStridedIntervalSet
from .valueset import ValueSet
from .ifproxy import IfProxy
from ..ast.base import Base
from ..bv import BVV
