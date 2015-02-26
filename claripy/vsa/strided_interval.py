import fractions
import functools
import math
import itertools
import logging

logger = logging.getLogger('claripy.vsa.strided_interval')

from .decorators import expand_ifproxy
from ..backend import BackendObject

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
                o = o._reverse()

            #__import__('ipdb').set_trace()
            ## We are working on two instances that have different endianness!
            #if o.is_integer(): o = o._reverse()
            #elif self.is_integer(): self = self._reverse()
            #elif self._reversed: self = self._reverse()
            #else: o = o._reverse()

        ret = f(self, o)
        if self_reversed and isinstance(ret, StridedInterval):
            ret = ret.reverse()
        return ret

    return normalizer

si_id_ctr = itertools.count()

# Whether DiscreteStridedIntervalSet should be used or not. Sometimes we manually set it to False to allow easy
# implementation of test cases.
allow_dsis = True

def lcm(a, b):
    return a * b // fractions.gcd(a, b)

class StridedInterval(BackendObject):
    '''
    A Strided Interval is represented in the following form:
        stride[lower_bound, upper_bound]
    For more details, please refer to relevant papers like TIE and WYSINWYE.
    '''
    def __init__(self, name=None, bits=0, stride=None, lower_bound=None, upper_bound=None, uninitialized=False):
        self._name = name

        if self._name is None:
            self._name = "SI_%d" % si_id_ctr.next()

        self._bits = bits
        self._stride = stride
        self._lower_bound = lower_bound
        self._upper_bound = upper_bound

        self._reversed = False

        self.uninitialized = uninitialized

        if self._upper_bound != None and bits == 0:
            self._bits = self._min_bits()

        if self._upper_bound is None:
            self._upper_bound = StridedInterval.max_int(self.bits)

        if self._lower_bound is None:
            self._lower_bound = StridedInterval.min_int(self.bits)

    def __repr__(self):
        s = ""
        if self.is_empty():
            s = '%s<%d>[EmptySI]' % (self._name, self._bits)
        else:
            s = '%s<%d>0x%x[%s, %s]%s' % (self._name, self._bits, self._stride,
                                        self._lower_bound if type(self._lower_bound) == str else hex(self._lower_bound),
                                        self._upper_bound if type(self._upper_bound) == str else hex(self._upper_bound),
                                        'R' if self._reversed else '')

        if self.uninitialized:
            s += "(uninit)"

        return s

    @property
    def name(self):
        return self._name

    @property
    def reversed(self):
        return self._reversed

    def normalize(self):
        if self.bits == 8 and self.reversed:
            self._reversed = False

        if self.lower_bound == self.upper_bound:
            self._stride = 0

        if self.bits == 1 and self.lower_bound < 0:
            lb = abs(self.upper_bound)
            self.upper_bound = abs(self.lower_bound)
            self.lower_bound = lb

        if self._stride < 0:
            raise Exception("Why does this happen?")

        return self

    def eval(self, n):
        results = []

        lb = self.lower_bound

        if self.stride == 0 and n > 0:
            results.append(self.lower_bound)
        else:
            while len(results) < n and lb <= self.upper_bound:
                results.append(lb)
                lb += self.stride

        return results

    @staticmethod
    def top(bits, name=None, signed=False, uninitialized=False):
        '''
        Get a TOP StridedInterval

        :return:
        '''
        if signed:
            return StridedInterval(name=name,
                                   bits=bits,
                                   stride=1,
                                   lower_bound=StridedInterval.min_int(bits),
                                   upper_bound=StridedInterval.max_int(bits - 1),
                                   uninitialized=uninitialized)
        else:
            return StridedInterval(name=name,
                                   bits=bits,
                                   stride=1,
                                   lower_bound=0,
                                   upper_bound=StridedInterval.max_int(bits),
                                   uninitialized=uninitialized)

    @staticmethod
    def empty(bits):
        return StridedInterval(bits=bits,
                               stride=0,
                               lower_bound=-1,
                               upper_bound=-2)

    def __len__(self):
        '''
        Get the length in bits of this variable.
        :return:
        '''
        return self._bits

    def _get_signed_val(self, v):
        v = v.copy()

        if v._bits > 1:
            if v.upper_bound > v.max_int(v._bits - 1):
                # This is a negative number
                mask = (1 << v._bits) - 1
                v.upper_bound = -(((-v.upper_bound) & mask) - 1)
            if v.lower_bound > v.max_int(v._bits - 1):
                # This is a negative number
                mask = (1 << v._bits) - 1
                v.lower_bound = -(((-v.lower_bound) & mask) - 1)
            if v.lower_bound >= v.upper_bound:
                t = v.upper_bound
                v.upper_bound = v.lower_bound
                v.lower_bound = t

        return v

    @normalize_types
    def __eq__(self, o):
        if self.upper_bound < self.max_int(self.bits - 1) and not o.is_empty():
            o = self._get_signed_val(o)

        if (self.stride == o.stride and
                    self.lower_bound == o.lower_bound and
                    self.upper_bound == o.upper_bound):
            # They are definitely equal
            # FIXME: This is incorrect... should be MaybeResult()
            # FIXME: Only when self.is_integer() == True can it returns TrueResult()
            return TrueResult()
        elif self.upper_bound < o.lower_bound or o.upper_bound < self.lower_bound:
            return FalseResult()
        else:
            stride = fractions.gcd(self.stride, o.stride)
            remainder_1 = self.upper_bound % stride
            remainder_2 = o.upper_bound % stride
            if remainder_1 == remainder_2:
                return MaybeResult()
            else:
                return FalseResult()

    @normalize_types
    def __ne__(self, o):
        return ~(self == o)

    @normalize_types
    def __gt__(self, other):
        if self.lower_bound > other.upper_bound:
            return TrueResult()
        elif self.upper_bound <= other.lower_bound:
            return FalseResult()
        return MaybeResult()

    @normalize_types
    def __lt__(self, other):
        return ~(self > other) & ~(self == other)

    @normalize_types
    def __le__(self, other):
        return ~(self > other)

    @normalize_types
    def __add__(self, o):
        return self.add(o, allow_overflow=True)

    @normalize_types
    def __sub__(self, o):
        return self.add(o.neg(), allow_overflow=True)

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

    @property
    def size(self):
        logger.warning("StridedInterval.size will be deprecated soon. Please use StridedInterval.cardinality instead.")
        return self.cardinality

    @property
    def cardinality(self):
        if self._stride == 0:
            if self.is_empty():
                return 0
            else:
                return 1
        else:
            return (self._upper_bound - self._lower_bound) / self._stride

    @staticmethod
    def highbit(k):
        return 1 << (k - 1)

    def copy(self):
        si = StridedInterval(name=self._name,
                               bits=self.bits,
                               stride=self.stride,
                               lower_bound=self.lower_bound,
                               upper_bound=self.upper_bound,
                               uninitialized=self.uninitialized)
        si._reversed = self._reversed
        return si

    def nameless_copy(self):
        si = StridedInterval(name=None,
                             bits=self.bits,
                             stride=self.stride,
                             lower_bound=self.lower_bound,
                             upper_bound=self.upper_bound)
        si._reversed = self._reversed
        return si

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
        if not self.is_empty():
            return self.upper_bound
        else:
            # It is empty!
            return None

    @property
    def min(self):
        if not self.is_empty():
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
    def _to_negative(a, bits):
        return -((1 << bits) - a)

    @staticmethod
    def upper(bits, i, stride):
        '''

        :return:
        '''
        if stride >= 1:
            offset = i % stride
            max = StridedInterval.max_int(bits) #pylint:disable=redefined-builtin
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
            min = StridedInterval.min_int(bits) #pylint:disable=redefined-builtin
            min_offset = min % stride

            if offset >= min_offset:
                o = min + (offset - min_offset)
            else:
                o = min + ((offset + stride) - min_offset)
            return o
        else:
            return StridedInterval.min_int(bits)

    def is_empty(self):
        return self._stride == 0 and self._lower_bound > self._upper_bound

    def is_top(self):
        '''
        If this is a TOP value
        :return: True if this is a TOP
        '''
        return (self.stride == 1 and
                ((
                    self.lower_bound == StridedInterval.min_int(self.bits) and
                    self.upper_bound == StridedInterval.max_int(self.bits - 1)
                 )
                 or
                 (
                     self.lower_bound == 0 and
                     self.upper_bound == StridedInterval.max_int(self.bits)
                 ))
                )

    def is_integer(self):
        '''
        If this is an integer, i.e. self.lower_bound == self.upper_bound
        :return: True if this is an integer, False otherwise
        '''
        return self.lower_bound == self.upper_bound

    def add(self, b, allow_overflow=True): #pylint:disable=unused-argument
        '''
        Operation add
        :param b:
        :return: self + b
        '''
        new_bits = max(self.bits, b.bits)

        lb_ = self.lower_bound + b.lower_bound
        ub_ = self.upper_bound + b.upper_bound
        uninitialized = self.uninitialized or b.uninitialized

        # This implementation (as in BAP 0.8) will yield imprecise result when dealing with overflows!
        # lb_underflow_ = (lb_ < StridedInterval.min_int(self.bits))
        # ub_overflow_ = (ub_ > StridedInterval.max_int(self.bits))
        # overflow = lb_underflow_ or ub_overflow_
        overflow = False
        if (lb_ < StridedInterval.min_int(self.bits) and ub_ > StridedInterval.min_int(self.bits) and ub_ < StridedInterval.max_int(self.bits)) or \
                (lb_ >= StridedInterval.min_int(self.bits) and lb_ <= StridedInterval.max_int(self.bits) and ub_ > StridedInterval.max_int(self.bits)):
            overflow = True

        # Take the GCD of two operands' strides
        stride = fractions.gcd(self.stride, b.stride)

        if overflow:
            if b.is_integer() and b.lower_bound >> (new_bits - 1) == 1:
                # Treat it as a minus then
                operand = - ((0 - b.lower_bound) & ((1 << new_bits) - 1))
                return self.__add__(operand)
            else:
                return self.top(new_bits, uninitialized=uninitialized)
        else:
            # new_lb = self.lower(new_bits, lb_, stride) if lb_underflow_ else lb_
            # new_ub = self.upper(new_bits, ub_, stride) if ub_overflow_ else ub_
            mask = StridedInterval.max_int(self.bits)
            new_lb = lb_
            if new_lb > mask:
                new_lb = new_lb & mask
            new_ub = ub_
            if new_ub > mask:
                new_ub = new_ub & mask

            return StridedInterval(bits=new_bits, stride=stride, lower_bound=new_lb, upper_bound=new_ub,
                                   uninitialized=uninitialized)

    def neg(self):
        '''
        Operation neg
        :return: -self
        '''
        # TODO: Finish it
        if not self.is_top():
            new_lb = -self.lower_bound
            new_ub = -self.upper_bound
            return StridedInterval(bits=self.bits, stride=self.stride, lower_bound=new_ub, upper_bound=new_lb)
        else:
            return StridedInterval.top(self.bits)

    def bitwise_not(self):
        '''
        Operation not
        :return: ~self
        '''
        if not self.is_top():
            new_lb = ~self.lower_bound
            new_ub = ~self.upper_bound
            return StridedInterval(bits=self.bits, stride=self.stride, lower_bound=new_ub, upper_bound=new_lb)
        else:
            return StridedInterval.top(bits=self.bits)

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
        '''
        Operation or
        :param b: The other operand
        :return: self | b
        '''
        assert self.bits == b.bits

        # Special handling for integers
        # TODO: Is this special handling still necessary?
        if self.stride == 0 and self.lower_bound == self.upper_bound:
            # self is an integer
            t = self._ntz(b.stride)
        elif b.stride == 0 and b.lower_bound == b.upper_bound:
            # b is an integer
            t = self._ntz(self.stride)
        else:
            t = min(self._ntz(self.stride), self._ntz(b.stride))
        stride_ = 1 << t
        lowbits = (self.lower_bound | b.lower_bound) & (stride_ - 1)

        # TODO: Make this function looks better
        r_1 = self.lower_bound < 0
        r_2 = self.upper_bound < 0
        r_3 = b.lower_bound < 0
        r_4 = b.upper_bound < 0

        lb_ = 0
        ub_ = 0
        if (r_1, r_2, r_3, r_4) == (True, True, True, True):
            lb_ = StridedInterval.min_or(self.bits, self.lower_bound, self.upper_bound, b.lower_bound, b.upper_bound)
            ub_ = StridedInterval.max_or(self.bits, self.lower_bound, self.upper_bound, b.lower_bound, b.upper_bound)
        elif (r_1, r_2, r_3, r_4) == (True, True, False, False):
            lb_ = StridedInterval.min_or(self.bits, self.lower_bound, self.upper_bound, b.lower_bound, b.upper_bound)
            ub_ = StridedInterval.max_or(self.bits, self.lower_bound, self.upper_bound, b.lower_bound, b.upper_bound)
        elif (r_1, r_2, r_3, r_4) == (False, False, True, True):
            lb_ = StridedInterval.min_or(self.bits, self.lower_bound, self.upper_bound, b.lower_bound, b.upper_bound)
            ub_ = StridedInterval.max_or(self.bits, self.lower_bound, self.upper_bound, b.lower_bound, b.upper_bound)
        elif (r_1, r_2, r_3, r_4) == (False, False, False, False):
            lb_ = StridedInterval.min_or(self.bits, self.lower_bound, self.upper_bound, b.lower_bound, b.upper_bound)
            ub_ = StridedInterval.max_or(self.bits, self.lower_bound, self.upper_bound, b.lower_bound, b.upper_bound)
        elif (r_1, r_2, r_3, r_4) == (True, True, True, False):
            lb_ = self.lower_bound
            ub_ = 1
        elif (r_1, r_2, r_3, r_4) == (True, False, True, True):
            lb_ = b.lower_bound
            ub_ = 1
        elif (r_1, r_2, r_3, r_4) == (True, False, True, False):
            lb_ = min(self.lower_bound, b.lower_bound)
            ub_ = StridedInterval.max_or(self.bits, 0, self.upper_bound, 0, b.upper_bound)
        elif (r_1, r_2, r_3, r_4) == (True, False, False, False):
            lb_ = StridedInterval.min_or(self.bits, self.lower_bound, 1, b.lower_bound, b.upper_bound)
            ub_ = StridedInterval.max_or(self.bits, 0, self.upper_bound, b.lower_bound, b.upper_bound)
        elif (r_1, r_2, r_3, r_4) == (False, False, True, False):
            lb_ = StridedInterval.min_or(self.bits, self.lower_bound, self.upper_bound, b.lower_bound, 1)
            ub_ = StridedInterval.max_or(self.bits, self.lower_bound, self.upper_bound, b.lower_bound, b.upper_bound)
        else:
            raise ArithmeticError("Impossible")

        highmask = ~(stride_ - 1)
        ret = StridedInterval(bits=self.bits, stride=stride_, lower_bound=(lb_ & highmask) | lowbits,
                               upper_bound=(ub_ & highmask) | lowbits)
        ret.normalize()

        return ret

    def bitwise_and(self, b):
        '''
        Operation and
        :param b: The other operand
        :return:
        '''

        def number_of_ones(n):
            ctr = 0
            while n > 0:
                ctr += 1
                n &= n - 1

            return ctr

        # If only one bit is set in b, we can make it more precise
        if b.is_integer():
            if b.lower_bound == (1 << (b.bits - 1)):
                # It's testing the sign bit
                stride = 1 << (b.bits - 1)
                if self.lower_bound < 0:
                    if self.upper_bound >= 0:
                        return StridedInterval(bits=b.bits, stride=stride, lower_bound=0, upper_bound=stride)
                    else:
                        return StridedInterval(bits=b.bits, stride=0, lower_bound=stride, upper_bound=stride)
                else:
                    if self.lower_bound >= stride and self.upper_bound >= stride:
                        return StridedInterval(bits=b.bits, stride=0, lower_bound=stride, upper_bound=stride)
                    elif self.lower_bound < stride and self.upper_bound >= stride:
                        return StridedInterval(bits=b.bits, stride=stride, lower_bound=0, upper_bound=stride)
                    else:
                        return StridedInterval(bits=b.bits, stride=0, lower_bound=0, upper_bound=0)

            elif number_of_ones(b.lower_bound) == 1:
                if self.lower_bound < 0 and self.upper_bound > 0:
                    mask = (2 ** self.bits) - 1
                    s = self.copy()
                    s.lower_bound = self.lower_bound & mask
                    if s.lower_bound > s.upper_bound:
                        t = s.upper_bound
                        s.upper_bound = s.lower_bound
                        s.lower_bound = t

                else:
                    s = self

                first_one_pos = self._ntz(b.lower_bound)

                stride = 2 ** first_one_pos
                if s.lower_bound <= stride and s.upper_bound >= stride:
                    return StridedInterval(bits=s.bits, stride=stride, lower_bound=0, upper_bound=stride)
                elif s.upper_bound < stride:
                    return StridedInterval(bits=s.bits, stride=0, lower_bound=0, upper_bound=0)
                else:
                    return StridedInterval(bits=s.bits, stride=0, lower_bound=stride, upper_bound=stride)

        return self.bitwise_not().bitwise_or(b.bitwise_not()).bitwise_not()

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

            if expr.is_integer():
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

    def concat(self, b):
        # Zero-extend
        a = self.nameless_copy()
        a._bits += b.bits

        new_si = a.lshift(b.bits)
        new_b = b.copy()
        # Zero-extend b
        new_b._bits = new_si.bits

        if new_si.is_integer():
            # We can be more precise!
            new_si._bits = new_b.bits
            new_si._stride = new_b.stride
            new_si._lower_bound = new_si.lower_bound + b.lower_bound
            new_si._upper_bound = new_si.upper_bound + b.upper_bound
            return new_si
        else:
            return new_si.bitwise_or(new_b)

    def extract(self, high_bit, low_bit):
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
        # FIXME: This implementation is buggy and needs rewritten

        if self.extract(self.bits - 1, self.bits - 1).eval(2) == [ 0 ]:
            return self.zero_extend(new_length)

        si = self.copy()
        mask = (2 ** new_length - 1) - (2 ** self.bits - 1)
        si._lower_bound = si._lower_bound | mask
        si._upper_bound = si._upper_bound | mask
        si._bits = new_length

        return si

    def zero_extend(self, new_length):
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
        The union operation. It guarantees to return a _single_ StridedInterval.

        :param b: Operand.
        :return: A new StridedInterval
        """
        if self._reversed != b._reversed:
            logger.warning('Incoherent reversed flag between operands %s and %s', self, b)

        if self.is_empty():
            return b
        if b.is_empty():
            return self

        if self.is_integer() and b.is_integer():
            u = max(self.upper_bound, b.upper_bound)
            l = min(self.lower_bound, b.lower_bound)
            return StridedInterval(bits=self.bits, stride=u - l, lower_bound=l, upper_bound=u)

        new_stride = fractions.gcd(self.stride, b.stride)
        assert new_stride >= 0

        remainder_1 = self.lower_bound % new_stride if new_stride > 0 else 0
        remainder_2 = b.lower_bound % new_stride if new_stride > 0 else 0
        u = max(self.upper_bound, b.upper_bound)
        l = min(self.lower_bound, b.lower_bound)
        if remainder_1 == remainder_2:
            return StridedInterval(bits=self.bits, stride=new_stride, lower_bound=l, upper_bound=u)
        else:
            new_stride = fractions.gcd(abs(remainder_1 - remainder_2), new_stride)
            return StridedInterval(bits=self.bits, stride=new_stride, lower_bound=l, upper_bound=u)

    @normalize_types
    def intersection(self, b):
        if self.is_empty() or b.is_empty():
            return StridedInterval.empty(self.bits)

        assert self.bits == b.bits

        ret = None

        l = max(self.lower_bound, b.lower_bound)
        u = min(self.upper_bound, b.upper_bound)

        if self.stride == 0 and b.stride == 0:
            if self.lower_bound == b.lower_bound:
                ret = StridedInterval(bits=self.bits,
                                      stride=self.stride,
                                      lower_bound=self.lower_bound,
                                      upper_bound=self.upper_bound)
            else:
                ret = StridedInterval.empty(self.bits)
        elif self.stride == 0:
            if (b.lower_bound - self.lower_bound) % b.stride == 0 and \
                self.lower_bound >= b.lower_bound and \
                self.lower_bound <= b.upper_bound:
                ret = StridedInterval(bits=self.bits,
                                      stride=self.stride,
                                      lower_bound=self.lower_bound,
                                      upper_bound=self.upper_bound)
            else:
                ret = StridedInterval.empty(self.bits)
        elif b.stride == 0:
            if (b.lower_bound - self.lower_bound) % self.stride == 0 and \
                b.lower_bound >= self.lower_bound and \
                b.lower_bound <= self.upper_bound:
                ret = StridedInterval(bits=self.bits,
                                      stride=b.stride,
                                      lower_bound=b.lower_bound,
                                      upper_bound=b.upper_bound)
            else:
                ret = StridedInterval.empty(self.bits)
        else:
            new_stride = lcm(self.stride, b.stride)
            if (
                self.lower_bound % new_stride == 0 and
                b.lower_bound % new_stride  == 0
               ) or \
                    self.lower_bound == b.lower_bound: # More precise than the implementation in BAP 0.8
                u = u - ((u - l) % new_stride)
                if u >= l:
                    ret = StridedInterval(bits=self.bits,
                                          stride=new_stride,
                                          lower_bound=l,
                                          upper_bound=u)
                else:
                    ret = StridedInterval.empty(self.bits)
            else:
                ret = StridedInterval(bits=self.bits,
                                      stride=1,
                                      lower_bound=l,
                                      upper_bound=u)

        ret.normalize()
        return ret

    @normalize_types
    def widen(self, b):
        ret = None

        if self.is_empty() and not b.is_empty():
            ret = StridedInterval.top(bits=self.bits)

        elif self.is_empty():
            ret = b

        elif b.is_empty():
            ret = self

        else:
            new_stride = fractions.gcd(self.stride, b.stride)
            l = StridedInterval.lower(self.bits, self.lower_bound, new_stride) + 2 if b.lower_bound < self.lower_bound else self.lower_bound
            u = StridedInterval.upper(self.bits, self.upper_bound, new_stride) - 2 if b.upper_bound > self.upper_bound else self.upper_bound
            if new_stride == 0:
                if self.is_integer() and b.is_integer():
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
        :return:
        """

        if self.bits == 8:
            # No need for reversing
            return self.copy()

        if self.is_top():
            # A TOP is still a TOP after reversing
            si = self.copy()
            si._reversed = False
            return si

        else:
            if not self.is_integer():
                # We really don't want to do that. Something is wrong.
                logger.warning('Reversing a real strided-interval %s is bad', self)
                #__import__('ipdb').set_trace()

            # Reversing an integer is easy
            rounded_bits = ((self.bits + 7) / 8) * 8
            bytes = [ ]
            si = None

            for i in xrange(0, rounded_bits, 8):
                b = self.extract(min(i + 7, self.bits - 1), i)
                bytes.append(b)

            for b in bytes:
                si = b if si is None else si.concat(b)

            return si

    def _ntz(self, x):
        '''
        Get the position of first non-zero bit
        :param x:
        :return:
        '''
        if x == 0:
            return 0
        y = (~x) & (x - 1)  # There is actually a bug in BAP until 0.8

        def bits(y):
            n = 0
            while y != 0:
                n += 1
                y >>= 1
            return n

        return bits(y)

from ..errors import ClaripyOperationError
from .bool_result import TrueResult, FalseResult, MaybeResult
from . import discrete_strided_interval_set
from .discrete_strided_interval_set import DiscreteStridedIntervalSet
from .valueset import ValueSet
from .ifproxy import IfProxy
from ..ast.base import Base
from ..bv import BVV
