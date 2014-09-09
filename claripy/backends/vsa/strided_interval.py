import fractions

class StridedInterval(object):
    '''
    A Strided Interval is represented in the following form:
        stride[lower_bound, upper_bound]
    For more details, please refer to relevant papers like TIE and WYSINWYE.
    '''
    NEG_INF = 'NEG_INF'
    INF = 'INF'

    def __init__(self, bits=0, stride=None, lower_bound=NEG_INF, upper_bound=INF):
        self._bits = bits
        self._stride = stride
        self._lower_bound = lower_bound
        self._upper_bound = upper_bound

    def __repr__(self):
        if self.empty:
            return '[Empty]'
        else:
            return '<%d>%d[%s, %s]' % (self._bits, self._stride, \
                                       self._lower_bound if type(self._lower_bound) == str else str(self._lower_bound), \
                                       self._upper_bound if type(self._upper_bound) == str else str(self._upper_bound))

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

    def maxi(self, k):
        return self.highbit(k - 1)

    def mini(self, k):
        return self.extend(k, self.highbit(k))

    def upper(self, bits, i, stride):
        '''

        :return:
        '''
        if stride >= 1:
            offset = i % stride
            max = self.maxi(bits)
            max_offset = max % stride

            if max_offset >= offset:
                o = max - (max_offset - offset)
            else:
                o = max - ((max_offset + stride) - offset)
            return o
        else:
            return self.maxi(bits)

    def lower(self, bits, i, stride):
        '''

        :return:
        '''
        if stride >= 1:
            offset = i % stride
            min = self.mini(bits)
            min_offset = min % offset

            if offset >= min_offset:
                o = min + (offset - min_offset)
            else:
                o = min + ((offset + stride) - min_offset)
            return o
        else:
            return self.mini(bits)

    @property
    def top(self):
        '''
        If this is a TOP value
        :return: True if this is a TOP
        '''
        raise Exception('Not implemented')
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
        lb_underflow_ = (lb_ < self.mini(self.bits))
        ub_overflow_ = (ub_ > self.maxi(self.bits))
        overflow = lb_underflow_ or ub_overflow_
        stride = fractions.gcd(self.stride, b.stride)

        if overflow:
            return self.top(self.bits)
        else:
            lb_ = self.extend(lb_, self.bits)
            ub_ = self.extend(ub_, self.bits)
            new_lb = self.lower(self.bits, lb_, stride) if lb_underflow_ else lb_
            new_ub = self.upper(self.bits, ub_, stride) if ub_overflow_ else ub_

            return StridedInterval(bits=self.bits, stride=stride, lower_bound=new_lb, upper_bound=new_ub)

    def neg(self):
        '''
        Operation neg
        :return: ~self
        '''
        raise Exception('Not implemented')