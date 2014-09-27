import fractions
import functools
import math

from ..expression import E

def normalize_types(f):
    @functools.wraps(f)
    def normalizer(self, o):
        '''
        Convert any object to an object that we can process.
        '''
        if type(o) is E:
            o = o._model
        if type(self) is E:
            e = e._model
        if type(o) in (int, long):
            o = StridedInterval(bits=StridedInterval.min_bits(o), stride=0, lower_bound=o, upper_bound=o)
        if type(self) in (int, long):
            self = StridedInterval(bits=StridedInterval.min_bits(self), stride=0, lower_bound=self, upper_bound=self)
        return f(self, o)

    return normalizer

class StridedInterval(object):
    '''
    A Strided Interval is represented in the following form:
        stride[lower_bound, upper_bound]
    For more details, please refer to relevant papers like TIE and WYSINWYE.
    '''

    def __init__(self, name=None, bits=0, stride=None, lower_bound=None, upper_bound=None):
        self._name = name
        self._bits = bits
        self._stride = stride
        self._lower_bound = lower_bound
        self._upper_bound = upper_bound

        if self._upper_bound != None and bits == 0:
            self._bits = self._min_bits()

        if self._upper_bound is None:
            self._upper_bound = StridedInterval.max_int(self.bits)

        if self._lower_bound is None:
            self._lower_bound = StridedInterval.min_int(self.bits)

    def __repr__(self):
        if self.is_empty():
            return '%s<%d>[EmptySI]' % (self._name, self._bits)
        else:
            return '%s<%d>%d[%s, %s]' % (self._name, self._bits, self._stride,
                                       self._lower_bound if type(self._lower_bound) == str else str(self._lower_bound),
                                       self._upper_bound if type(self._upper_bound) == str else str(self._upper_bound))

    def normalize(self):
        if self.lower_bound == self.upper_bound:
            self._stride = 0
        if self._stride < 0:
            raise Exception("Why does this happen?")

    @staticmethod
    def top(bits, signed=False):
        '''
        Get a TOP StridedInterval

        :return:
        '''
        if signed:
            return StridedInterval(bits=bits,
                               stride=1,
                               lower_bound=StridedInterval.min_int(bits),
                               upper_bound=StridedInterval.max_int(bits - 1))
        else:
            return StridedInterval(bits=bits,
                               stride=1,
                               lower_bound=0,
                               upper_bound=StridedInterval.max_int(bits))

    def __len__(self):
        '''
        Get the length in bits of this variable. It should be a multiple of 8.
        :return:
        '''
        return (self._bits + 7) / 8 * 8

    @normalize_types
    def __eq__(self, o):
        # TODO: Currently we are not comparing the bits
        return ( # self._bits == o._bits and
            self._stride == o._stride
            and self._lower_bound == o._lower_bound
            and self._upper_bound == o._upper_bound)

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

    @normalize_types
    def __or__(self, other):
        return self.bitwise_or(other)

    @normalize_types
    def __and__(self, other):
        return self.bitwise_and(other)

    @normalize_types
    def __xor__(self, other):
        return self.bitwise_xor(other)

    @property
    def size(self):
        if self._stride == 0:
            return 0
        else:
            return ((self._upper_bound - self._lower_bound) / self._stride)

    @staticmethod
    def highbit(k):
        return (1 << (k - 1))

    def copy(self):
        return StridedInterval(name=self._name,
                               bits=self.bits,
                               stride=self.stride,
                               lower_bound=self.lower_bound,
                               upper_bound=self.upper_bound)

    @property
    def lower_bound(self):
        return self._lower_bound

    @property
    def upper_bound(self):
        return self._upper_bound

    @property
    def bits(self):
        return self._bits

    @property
    def stride(self):
        return self._stride

    @property
    def max(self):
        raise Exception('Not implemented')

    @property
    def min(self):
        raise Exception('Not implemented')

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
            return int(math.log(val, 2) + 1)

    @staticmethod
    def max_int(k):
        return StridedInterval.highbit(k + 1) - 1

    @staticmethod
    def min_int(k):
        return -StridedInterval.highbit(k)

    def upper(self, bits, i, stride):
        '''

        :return:
        '''
        if stride >= 1:
            offset = i % stride
            max = StridedInterval.max_int(bits)
            max_offset = max % stride

            if max_offset >= offset:
                o = max - (max_offset - offset)
            else:
                o = max - ((max_offset + stride) - offset)
            return o
        else:
            return StridedInterval.max_int(bits)

    def lower(self, bits, i, stride):
        '''

        :return:
        '''
        if stride >= 1:
            offset = i % stride
            min = StridedInterval.min_int(bits)
            min_offset = min % offset

            if offset >= min_offset:
                o = min + (offset - min_offset)
            else:
                o = min + ((offset + stride) - min_offset)
            return o
        else:
            return StridedInterval.min_int(bits)

    def is_empty(self):
        return (self._stride == 0 and self._lower_bound > self._upper_bound)

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
        return (self.lower_bound == self.upper_bound)

    def add(self, b, allow_overflow=True):
        '''
        Operation add
        :param b:
        :return: self + b
        '''
        assert self.bits == b.bits

        lb_ = self.lower_bound + b.lower_bound
        ub_ = self.upper_bound + b.upper_bound
        lb_underflow_ = (lb_ < StridedInterval.min_int(self.bits))
        ub_overflow_ = (ub_ > StridedInterval.max_int(self.bits))
        overflow = lb_underflow_ or ub_overflow_

        # Take the GCD of two operands' strides
        stride = fractions.gcd(self.stride, b.stride)

        if overflow:
            return self.top(self.bits)
        else:
            new_lb = self.lower(self.bits, lb_, stride) if lb_underflow_ else lb_
            new_ub = self.upper(self.bits, ub_, stride) if ub_overflow_ else ub_

            return StridedInterval(bits=self.bits, stride=stride, lower_bound=new_lb, upper_bound=new_ub)

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
            return StridedInterval.top()

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
            return StridedInterval.top()

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
                    return (tmp1 | d)
                elif tmp2 >= c:
                    return (tmp2 | b)
            m = m >> 1

    def bitwise_or(self, b):
        '''
        Operation or
        :param b: The other operand
        :return: self | b
        '''
        def ntz(x):
            '''
            Get the position of first non-zero bit
            :param x:
            :return:
            '''
            if x == 0:
                return 0
            y = (~x) & (x - 1) # There is actually a bug in BAP until 0.8

            def bits(n, y):
                if y == 0:
                    return n
                else:
                    return bits(n + 1, y >> 1)

            return bits(0, y)

        assert self.bits == b.bits

        # Special handling for integers
        # TODO: Is this special handling still necessary?
        if self.stride == 0 and self.lower_bound == self.upper_bound:
            # self is an integer
            t = ntz(b.stride)
        elif b.stride == 0 and b.lower_bound == b.upper_bound:
            # b is an integer
            t = ntz(self.stride)
        else:
            t = min(ntz(self.stride), ntz(b.stride))
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
            def round(max, x):
                if x < 0 or x > max:
                    return max
                else:
                    return x

            if type(expr) in [int, long]:
                return (expr, expr)

            assert type(expr) is StridedInterval

            if expr.stride == 1 and expr.lower_bound == expr.upper_bound:
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

        return StridedInterval(bits=self.bits,
                               stride=max(self.stride >> upper, 0),
                               lower_bound=new_lower_bound,
                               upper_bound=new_upper_bound)

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

        return StridedInterval(bits=self.bits + shift_amount,
                               stride=max(self.stride << lower, 0),
                               lower_bound=new_lower_bound,
                               upper_bound=new_upper_bound)

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
            elif (self.upper_bound - self.lower_bound <= mask):
                return StridedInterval(bits=tok, stride=self.stride,
                                       lower_bound=(self.lower_bound & mask),
                                       upper_bound=(self.upper_bound & mask))
            else:
                # TODO: How can we do better here? For example, keep the stride information?
                return self.top(tok)

    def concat(self, b):
        new_si = self.lshift(b.bits)
        new_b = b.copy()
        # Extend b
        new_b._bits = new_si.bits

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

        return ret

    @normalize_types
    def union(self, b):
        '''
        The union operation
        :param b:
        :return:
        '''
        if self.is_empty():
            return b
        if b.is_empty():
            return self

        if self.is_integer() and b.is_integer():
            u = max(self.upper_bound, b.upper_bound)
            l = min(self.lower_bound, b.lower_bound)
            return StridedInterval(bits=self.bits, stride=u - l, lower_bound=l, upper_bound=u)

        new_stride = fractions.gcd(self.stride, b.stride)
        assert new_stride > 0

        remainder_1 = self.lower_bound % new_stride
        remainder_2 = b.lower_bound % new_stride
        u = max(self.upper_bound, b.upper_bound)
        l = min(self.lower_bound, b.lower_bound)
        if remainder_1 == remainder_2:
            return StridedInterval(bits=self.bits, stride=new_stride, lower_bound=l, upper_bound=u)
        else:
            new_stride = fractions.gcd(abs(remainder_1 - remainder_2), new_stride)
            return StridedInterval(bits=self.bits, stride=new_stride, lower_bound=l, upper_bound=u)