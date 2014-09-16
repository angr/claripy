import fractions
import functools
import math

def normalize_types(f):
    @functools.wraps(f)
    def normalizer(self, o):
        '''
        Convert any object to an object that we can process.
        '''
        if type(o) in (int, long):
            o = StridedInterval(bits=StridedInterval.min_bits(o), stride=1, lower_bound=o, upper_bound=o)
        if type(self) in (int, long):
            self = StridedInterval(bits=StridedInterval.min_bits(self), stride=1, lower_bound=self, upper_bound=self)
        return f(self, o)

    return normalizer

class StridedInterval(object):
    '''
    A Strided Interval is represented in the following form:
        stride[lower_bound, upper_bound]
    For more details, please refer to relevant papers like TIE and WYSINWYE.
    '''
    NEG_INF = -1
    INF = -2

    def __init__(self, name=None, bits=0, stride=None, lower_bound=NEG_INF, upper_bound=INF):
        self._name = name
        self._bits = bits
        self._stride = stride
        self._lower_bound = lower_bound
        self._upper_bound = upper_bound

        if self._upper_bound != self.INF and bits == 0:
            self._bits = self._min_bits()

    def __repr__(self):
        if self.empty:
            return '%s<%d>[EmptySI]' % (self._name, self._bits)
        else:
            return '%s<%d>%d[%s, %s]' % (self._name, self._bits, self._stride,
                                       self._lower_bound if type(self._lower_bound) == str else str(self._lower_bound),
                                       self._upper_bound if type(self._upper_bound) == str else str(self._upper_bound))
    @staticmethod
    def top():
        '''
        Get a TOP StridedInterval
        :return:
        '''
        raise NotImplementedError()

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
    def empty(self):
        return (self._stride == None and self._lower_bound == self.NEG_INF and self._upper_bound == self.INF)

    @property
    def size(self):
        if self._stride == 0:
            return 1
        else:
            return ((self._upper_bound - self._lower_bound) / self._stride)

    @staticmethod
    def highbit(k):
        return (1 << (k - 1))

    def extend(self, i, k):
        '''
        Cast i as a signed number

        :param i:
        :param k:
        :return:
        '''
        raise Exception('Not implemented')

    def truncate(self, i, k):
        '''
        Set the irrelevant upper bits of i to 0
        :param i:
        :param k:
        :return:
        '''
        raise Exception('Not implemented')

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

    def max_int(self, k):
        return StridedInterval.highbit(k) - 1

    def min_int(self, k):
        return -StridedInterval.highbit(k)

    def upper(self, bits, i, stride):
        '''

        :return:
        '''
        if stride >= 1:
            offset = i % stride
            max = self.max_int(bits)
            max_offset = max % stride

            if max_offset >= offset:
                o = max - (max_offset - offset)
            else:
                o = max - ((max_offset + stride) - offset)
            return o
        else:
            return self.max_int(bits)

    def lower(self, bits, i, stride):
        '''

        :return:
        '''
        if stride >= 1:
            offset = i % stride
            min = self.min_int(bits)
            min_offset = min % offset

            if offset >= min_offset:
                o = min + (offset - min_offset)
            else:
                o = min + ((offset + stride) - min_offset)
            return o
        else:
            return self.min_int(bits)

    def is_top(self):
        '''
        If this is a TOP value
        :return: True if this is a TOP
        '''
        # TODO: Finish it
        return False

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
        lb_underflow_ = (lb_ < self.min_int(self.bits))
        ub_overflow_ = (ub_ > self.max_int(self.bits))
        overflow = lb_underflow_ or ub_overflow_

        # Special cases for integers
        if self.is_integer():
            stride = b.stride
        elif b.is_integer():
            stride = self.stride
        else:
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
            new_lb = -self.lower_bound if self.lower_bound != self.NEG_INF else self.INF
            new_ub = -self.upper_bound if self.upper_bound != self.INF else self.NEG_INF
            return StridedInterval(bits=self.bits, stride=self.stride, lower_bound=new_ub, upper_bound=new_lb)
        else:
            return StridedInterval.top()

    def bitwise_not(self):
        '''
        Operation not
        :return: ~self
        '''
        if not self.is_top():
            new_lb = ~self.lower_bound if self.lower_bound != self.NEG_INF else self.INF
            new_ub = ~self.upper_bound if self.upper_bound != self.INF else self.NEG_INF
            return StridedInterval(bits=self.bits, stride=self.stride, lower_bound=new_ub, upper_bound=new_lb)
        else:
            return StridedInterval.top()

    @staticmethod
    def min_or(k, a, b, c, d):
        m = StridedInterval.highbit(k)
        while True:
            if m == 0:
                return a | c
            elif (~a & c & m) != 0:
                tmp = (a | m) & ~m
                if tmp <= b:
                    return tmp | c
            elif (a & ~c & m) != 0:
                tmp = (c + m) & ~m
                if tmp <= d:
                    return tmp | a
            m = m >> 1

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
            I have no idea what this function is doing.
            :param x:
            :return:
            '''
            y = (-x) & (x - 1)

            def bits(n, y):
                if y == 0:
                    return n
                else:
                    return bits(n + 1, y >> 1)

            return bits(0, y)

        assert self.bits == b.bits

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
        return StridedInterval(bits=self.bits, stride=stride_, lower_bound=(lb_ & highmask) | lowbits,
                               upper_bound=(ub_ & highmask) | lowbits)

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