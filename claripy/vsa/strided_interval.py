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

    @property
    def empty(self):
        return (self._stride == None and self._lower_bound == self.NEG_INF and self._upper_bound == self.INF)

    @property
    def size(self):
        if self._stride == 0:
            return 1
        else:
            return ((self._upper_bound - self._lower_bound) / self._stride)

    def highbit(self, k):
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
        assert val >= 0
        if val == 0:
            return 1
        return int(math.log(val, 2) + 1)

    def max_int(self, k):
        return self.highbit(k) - 1

    def min_int(self, k):
        return -self.highbit(k)

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
        :return: ~self
        '''
        # TODO: Finish it
        if not self.is_top():
            new_lb = -self.lower_bound if self.lower_bound != self.NEG_INF else self.INF
            new_ub = -self.upper_bound if self.upper_bound != self.INF else self.NEG_INF
            return StridedInterval(bits=self.bits, stride=self.stride, lower_bound=new_lb, upper_bound=new_ub)
        else:
            return StridedInterval.top()
