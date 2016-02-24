class WarrenMethods(object):
    """
        Methods as suggested in book.
        Hackers Delight.
    """
    @staticmethod
    def min_or(a, b, c, d, w):
        """
        Lower bound of result of ORing 2-intervals
        :param a: Lower bound of first interval
        :param b: Upper bound of first interval
        :param c: Lower bound of second interval
        :param d: Upper bound of second interval
        :param w: bit width
        :return: Lower bound of ORing 2-intervals
        """
        m = (1 << (w - 1))
        while m != 0:
            if ((~a) & c & m) != 0:
                temp = (a | m) & -m
                if temp <= b:
                    a = temp
                    break
            elif (a & (~c) & m) != 0:
                temp = (c | m) & -m
                if temp <= d:
                    c = temp
                    break
            m >>= 1
        return a | c

    @staticmethod
    def max_or(a, b, c, d, w):
        """
        Upper bound of result of ORing 2-intervals
        :param a: Lower bound of first interval
        :param b: Upper bound of first interval
        :param c: Lower bound of second interval
        :param d: Upper bound of second interval
        :param w: bit width
        :return: Upper bound of ORing 2-intervals
        """
        m = (1 << (w - 1))
        while m != 0:
            if (b & d & m) != 0:
                temp = (b - m) | (m - 1)
                if temp >= a:
                    b = temp
                    break
                temp = (d - m) | (m - 1)
                if temp >= c:
                    d = temp
                    break
            m >>= 1
        return b | d

    @staticmethod
    def min_and(a, b, c, d, w):
        """
        Lower bound of result of ANDing 2-intervals
        :param a: Lower bound of first interval
        :param b: Upper bound of first interval
        :param c: Lower bound of second interval
        :param d: Upper bound of second interval
        :param w: bit width
        :return: Lower bound of ANDing 2-intervals
        """
        m = (1 << (w - 1))
        while m != 0:
            if (~a & ~c & m) != 0:
                temp = (a | m) & -m
                if temp <= b:
                    a = temp
                    break
                temp = (c | m) & -m
                if temp <= d:
                    c = temp
                    break
            m >>= 1
        return a & c

    @staticmethod
    def max_and(a, b, c, d, w):
        """
        Upper bound of result of ANDing 2-intervals
        :param a: Lower bound of first interval
        :param b: Upper bound of first interval
        :param c: Lower bound of second interval
        :param d: Upper bound of second interval
        :param w: bit width
        :return: Upper bound of ANDing 2-intervals
        """
        m = (1 << (w - 1))
        while m != 0:
            if ((~d) & b & m) != 0:
                temp = (b & ~m) | (m - 1)
                if temp >= a:
                    b = temp
                    break
            elif (d & (~b) & m) != 0:
                temp = (d & ~m) | (m - 1)
                if temp >= c:
                    d = temp
                    break
            m >>= 1
        return b & d

    @staticmethod
    def min_xor(a, b, c, d, w):
        """
        Lower bound of result of XORing 2-intervals
        :param a: Lower bound of first interval
        :param b: Upper bound of first interval
        :param c: Lower bound of second interval
        :param d: Upper bound of second interval
        :param w: bit width
        :return: Lower bound of XORing 2-intervals
        """
        m = (1 << (w - 1))
        while m != 0:
            if ((~a) & c & m) != 0:
                temp = (a | m) & -m
                if temp <= b:
                    a = temp
            elif (a & (~c) & m) != 0:
                temp = (c | m) & -m
                if temp <= d:
                    c = temp
            m >>= 1
        return a ^ c

    @staticmethod
    def max_xor(a, b, c, d, w):
        """
        Upper bound of result of XORing 2-intervals
        :param a: Lower bound of first interval
        :param b: Upper bound of first interval
        :param c: Lower bound of second interval
        :param d: Upper bound of second interval
        :param w: bit width
        :return: Upper bound of XORing 2-intervals
        """
        m = (1 << (w - 1))
        while m != 0:
            if (b & d & m) != 0:
                temp = (b - m) | (m - 1)
                if temp >= a:
                    b = temp
                else:
                    temp = (d - m) | (m - 1)
                    if temp >= c:
                        d = temp
            m >>= 1
        return b ^ d


"""
Faithful reproduction of paper Signedness-agnostic program analysis: Precise integer bounds for low-level code

More details are in another journal paper: Interval analysis and machine arithmetic: Why signedness ignorance is bliss
This is meant to serve as a base implementation of wrapped intervals.
Any use of wrapped intervals should reuse this.
"""


class WrappedInterval(object):
    """
        Class representing a wrapped interval.
        Refer paper: Signedness-agnostic program analysis: Precise integer bounds for low-level code
    """

    def __init__(self, lower_bound, upper_bound, no_of_bits=32, is_bottom_flag=False):
        """
        Construct a new wrapped interval with provided lower and upper bounds.
        :return:
        """
        assert isinstance(lower_bound, int), "Provided Lower Bound is not integer. Expected Integer."
        assert isinstance(upper_bound, int), "Provided Upper Bound is not integer. Expected Integer."
        assert isinstance(no_of_bits, int), "No of bits is not integer. Expected Integer."
        assert no_of_bits > 0, "Number of bits should be greater than 0"

        # Convert lower bound and upper bound to sign agnostic representation
        self.lower_bound = WrappedInterval._get_sign_agnostic_repr(lower_bound, no_of_bits)
        self.upper_bound = WrappedInterval._get_sign_agnostic_repr(upper_bound, no_of_bits)
        self.no_of_bits = no_of_bits
        self.is_bottom_flag = is_bottom_flag

    @staticmethod
    def _get_sign_agnostic_repr(target_num, no_of_bits):
        """
        Returns sign agnostic representation of the provided number
        :param target_num: Target number to convert
        :param no_of_bits:  Maximum bit width
        :return: Number in sign agnostic representation
        Note: The return value will be always positive
        """
        return target_num & WrappedInterval._max_upper_bound(no_of_bits)

    @staticmethod
    def _get_top(no_of_bits):
        """
        Return TOP for the given number of bits
        :param no_of_bits: target number of bits
        :return: Interval representing TOP
        """
        return WrappedInterval(0, WrappedInterval._max_upper_bound(no_of_bits), no_of_bits=no_of_bits)

    @staticmethod
    def _get_bottom(no_of_bits):
        """
        Return Interval Representing Bottom
        :param no_of_bits: target number of bits
        :return: Interval representing BOTTOM
        """
        return WrappedInterval(0, WrappedInterval._max_upper_bound(no_of_bits), no_of_bits=no_of_bits,
                               is_bottom_flag=True)

    @staticmethod
    def _max_upper_bound(no_of_bits):
        """
        This function returns the maximum number that
        can be represented with given number of bits.
        :param no_of_bits: Number of bits
        :return: Maximum number that is possible i.e all ones 111...111
        Note: The return value will be always positive
        """
        assert no_of_bits >= 0, "Number of bits cannot be negative"
        return (1 << no_of_bits) - 1

    @staticmethod
    def _get_signed_repr(target_num, no_of_bits):
        """
        Return signed representation of the given number
        :param target_num: Number to be interpreted
        :param no_of_bits: Number of bits for number
        :return: Number in signed representation
        """
        msb_num = WrappedInterval._msb(target_num, no_of_bits)
        if msb_num == 1:
            # subtract 1 from number and get 1s complement
            # We need to limit this number of given number of bits
            target_num = (~(target_num - 1)) & WrappedInterval._max_upper_bound(no_of_bits)
            target_num *= -1
        return target_num

    @staticmethod
    def _mod_equals(op1, op2, no_of_bits):
        """
        Performs: Modular equality.
        Perform (op1 ==w op2) and return result with in no_of_bits
        Refer Section 3.2 of the paper.
        :param op1: operand 1
        :param op2: operand 2
        :param no_of_bits: number of bits to compare.
        :return: True/False => result of modular equality.
        """
        return (op1 & WrappedInterval._max_upper_bound(no_of_bits)) == \
               (op2 & WrappedInterval._max_upper_bound(no_of_bits))

    @staticmethod
    def _mod_sub(op1, op2, no_of_bits):
        """
        Performs: Modular subtraction.
        Perform (op1 - op2) and return result with in no_of_bits
        Refer Section 3 of the paper.
        :param op1: operand 1
        :param op2: operand 2
        :param no_of_bits: Width of the result.
        :return: result of modular subtraction.
        Note: The return value will be always positive
        """
        assert no_of_bits > 0, "Number of bits should be more than zero"
        return (op1 - op2) & WrappedInterval._max_upper_bound(no_of_bits)

    @staticmethod
    def _mod_add(op1, op2, no_of_bits):
        """
        Performs: Modular Addition.
        Perform (op1 + op2) and return result with in no_of_bits
        Refer Section 3 of the paper.
        :param op1: operand 1
        :param op2: operand 2
        :param no_of_bits: Width of the result.
        :return: result of modular addition.
        Note: The return value will be always positive
        """
        assert no_of_bits > 0, "Number of bits should be more than zero"
        return (op1 + op2) & WrappedInterval._max_upper_bound(no_of_bits)

    @staticmethod
    def _mod_mul(op1, op2, no_of_bits):
        """
        Performs: Modular Multiplication.
        Perform (op1 * op2) and return result with in no_of_bits
        Refer Section 3 of the paper.
        :param op1: operand 1
        :param op2: operand 2
        :param no_of_bits: Width of the result.
        :return: result of modular multiplication.
        Note: The return value will be always positive
        """
        assert no_of_bits > 0, "Number of bits should be more than zero"
        return (op1 * op2) & WrappedInterval._max_upper_bound(no_of_bits)

    @staticmethod
    def _mod_u_div(op1, op2, no_of_bits):
        """
        Performs: Unsigned Modular Division.
        Perform (op1 / op2) and return result with in no_of_bits
        Refer Section 3 of the paper.
        :param op1: operand 1
        :param op2: operand 2
        :param no_of_bits: Width of the result.
        :return: quotient of modular division.
        Note: The return value will be always positive
        """
        assert no_of_bits > 0, "Number of bits should be more than zero"
        return (op1 / op2) & WrappedInterval._max_upper_bound(no_of_bits)

    @staticmethod
    def _mod_s_div(op1, op2, no_of_bits):
        """
        Performs: Signed Modular Division.
        Perform (op1 / op2) and return result with in no_of_bits
        Refer Section 3 of the paper.
        :param op1: operand 1
        :param op2: operand 2
        :param no_of_bits: Width of the result.
        :return: quotient of modular division.
        Note: The return value will be always positive
        """
        assert no_of_bits > 0, "Number of bits should be more than zero"
        # convert the numbers into signed representation
        op1 = WrappedInterval._get_signed_repr(op1, no_of_bits)
        # converting to signed representation
        op2 = WrappedInterval._get_signed_repr(op2, no_of_bits)
        return (op1 / op2) & WrappedInterval._max_upper_bound(no_of_bits)

    @staticmethod
    def _mod_u_range_div(a, b, c, d, w):
        """
        Perform modular unsigned division of given range
        Refer 1:15 of paper:
        Interval analysis and machine arithmetic: Why signedness ignorance is bliss
        :param a: Lower bound of first operand
        :param b: Upper bound of first operand
        :param c: Lower bound of second operand
        :param d: Upper bound of second operand
        :param w: Bit width
        :return: Interval containing the result.
        """
        a_div_d = WrappedInterval._mod_u_div(a, d, w)
        b_div_c = WrappedInterval._mod_u_div(b, c, w)
        return WrappedInterval(a_div_d, b_div_c, no_of_bits=w)

    @staticmethod
    def _mod_s_range_div(a, b, c, d, w):
        """
        Perform modular signed division of given range
        Refer 1:16 of paper:
        Interval analysis and machine arithmetic: Why signedness ignorance is bliss
        :param a: Lower bound of first operand
        :param b: Upper bound of first operand
        :param c: Lower bound of second operand
        :param d: Upper bound of second operand
        :param w: Bit width
        :return: Interval containing the result.
        """
        msb_a = WrappedInterval._msb(a, w)
        msb_c = WrappedInterval._msb(c, w)
        # case 1
        if msb_a == msb_c and msb_c == 0:
            a_div_d = WrappedInterval._mod_s_div(a, d, w)
            b_div_c = WrappedInterval._mod_s_div(b, c, w)
            return WrappedInterval(a_div_d, b_div_c, no_of_bits=w)
        # case 2
        if msb_a == msb_c and msb_c == 1:
            a_div_d = WrappedInterval._mod_s_div(a, d, w)
            b_div_c = WrappedInterval._mod_s_div(b, c, w)
            return WrappedInterval(b_div_c, a_div_d, no_of_bits=w)
        # case 3
        if msb_a == 0 and msb_c == 1:
            b_div_d = WrappedInterval._mod_s_div(b, d, w)
            a_div_c = WrappedInterval._mod_s_div(a, c, w)
            return WrappedInterval(b_div_d, a_div_c, no_of_bits=w)
        # case 4
        if msb_a == 1 and msb_c == 0:
            b_div_d = WrappedInterval._mod_s_div(b, d, w)
            a_div_c = WrappedInterval._mod_s_div(a, c, w)
            return WrappedInterval(a_div_c, b_div_d, no_of_bits=w)

        assert False, "We should never reach here, Potential cause: Invalid return value my msb function"

    @staticmethod
    def _gap(src_interval, tar_interval):
        """
        Refer section 3.1; gap function
        :param src_interval: first argument or interval 1
        :param tar_interval: second argument or interval 2
        :return: Interval representing gap between two intervals
        """
        assert src_interval.no_of_bits == tar_interval.no_of_bits, "Number of bits should be same for operands"
        # use the same variable names as in paper
        w = src_interval.no_of_bits
        s = src_interval
        t = tar_interval
        (a, b) = (s.lower_bound, s.upper_bound)
        (c, d) = (t.lower_bound, t.upper_bound)

        w = s.no_of_bits
        # case 1
        if (not t.is_in_interval(b)) and (not s.is_in_interval(c)):
            return WrappedInterval(c, b, no_of_bits=w).get_complement()
        # otherwise
        return WrappedInterval._get_bottom(w)

    @staticmethod
    def _extend(src_interval, dst_interval):
        """
        Extend src interval to include destination
        Refer 1:11 of paper:
        Interval analysis and machine arithmetic: Why signedness ignorance is bliss
        :param src_interval: Interval to extend
        :param dst_interval: Interval to be extended to
        :return: Interval starting from src interval which also includes dst interval
        """
        s = src_interval
        t = dst_interval
        w = s.no_of_bits
        (a, _) = (s.lower_bound, s.upper_bound)
        (_, d) = (t.lower_bound, t.upper_bound)
        # case 1
        if t.is_interval_included(s):
            return t.copy()
        # case 2
        if s.is_interval_included(t):
            return s.copy()
        # case 3
        if t.is_interval_included(s.get_complement()):
            return WrappedInterval._get_top(w)
        # otherwise
        return WrappedInterval(a, d, no_of_bits=w)

    @staticmethod
    def _bigger(interval1, interval2):
        """
        Return interval with bigger cardinality
        Refer Section 3.1
        :param interval1: first interval
        :param interval2: second interval
        :return: Interval or interval2 whichever has greater cardinality
        """
        if interval2.get_size() > interval1.get_size():
            return interval2.copy()
        return interval1.copy()

    @staticmethod
    def _least_upper_bound(intervals_to_join):
        """
        Pseudo least upper bound.
        Join the given set of intervals into a big interval
        Refer section 3.1
        :param intervals_to_join: Intervals to join
        :return: Interval that contains all intervals
        """
        assert len(intervals_to_join) > 0, "No intervals to join"
        # Optimization: If we have only one interval, then return that interval as result
        if len(intervals_to_join) == 1:
            return intervals_to_join[0].copy()
        # Check if all intervals are of same width
        all_same = all(x.no_of_bits == intervals_to_join[0].no_of_bits for x in intervals_to_join)
        assert all_same, "All intervals to join should be same"
        # sort the intervals in increasing left bound
        sorted_intervals = sorted(intervals_to_join, key=lambda x: x.lower_bound)
        # Fig 3 of the paper
        w = intervals_to_join[0].no_of_bits
        f = WrappedInterval._get_bottom(w)
        g = WrappedInterval._get_bottom(w)
        for s in sorted_intervals:
            if s.is_top() or WrappedInterval._less_than_a(s.upper_bound, s.lower_bound, 0, w):
                # f <- extend(f, s)
                f = WrappedInterval._extend(f, s)
        for s in sorted_intervals:
            # g <- bigger(g, gap(f, s))
            g = WrappedInterval._bigger(g, WrappedInterval._gap(f, s))
            # f <- extend(f, s)
            f = WrappedInterval._extend(f, s)
        # Result
        return WrappedInterval._bigger(g, f.get_complement()).get_complement()

    @staticmethod
    def _less_than_a(num1, num2, a, no_of_bits):
        """
        Implements a less than equal operator as suggested in
        the paper
        Refer Section 3.
                Operator: b <=a c
                iff b -w a <= c -w a
        :param num1: b or num1
        :param num2:  c or num2
        :param a: width.
        :return: True if num1 <=a  num2 else False
        """
        num1_a = WrappedInterval._mod_sub(num1, a, no_of_bits)
        num2_a = WrappedInterval._mod_sub(num2, a, no_of_bits)
        return num1_a <= num2_a

    @staticmethod
    def _get_north_pole(no_of_bits):
        """
        Get interval representing north pole
        Refer Section 3.2, nsplit
        :param no_of_bits: Number of bits or w
        :return: Interval representing north pole
        """
        w = no_of_bits
        assert w > 0, "Number of bits should be more than 0"
        np_low = (1 << (w - 1)) - 1  # 01111111..111
        np_high = 1 << (w - 1)  # 100000..000
        return WrappedInterval(np_low, np_high, no_of_bits=w)

    @staticmethod
    def _get_south_pole(no_of_bits):
        """
        Get interval representing south pole
        Refer Section 3.2, ssplit
        :param no_of_bits: Number of bits or w
        :return: Interval representing south pole
        """
        w = no_of_bits
        assert w > 0, "Number of bits should be more than 0"
        sp_low = (1 << w) - 1  # 11111..111
        sp_high = 0  # 00000
        return WrappedInterval(sp_low, sp_high, no_of_bits=w)

    @staticmethod
    def _msb(target_number, no_of_bits):
        """
        Get the most significant bit of the given number
        :param target_number:Number for which bit needs to be fetched
        :param no_of_bits: Target bit size of given number
        :return: 1 or 0
        """
        return 1 if ((1 << (no_of_bits - 1)) & target_number) != 0 else 0

    @staticmethod
    def _signed_mul(a, b, c, d, w):
        """
        Implementation of signed multiplication
        Signed multiply the current interval with given interval
        Refer section 3.2 Analysing expression
        :param a: first lower bound
        :param b: first upper bound
        :param c: second lower bound
        :param d: second upper bound
        :param w: bit width
        :return: Interval representing result interval
        """

        msb_a = WrappedInterval._msb(a, w)
        msb_b = WrappedInterval._msb(b, w)
        msb_c = WrappedInterval._msb(c, w)
        msb_d = WrappedInterval._msb(d, w)
        # case 1
        if msb_a == msb_b and msb_b == msb_c and msb_c == msb_d and \
                ((b*d - a*c) <= WrappedInterval._max_upper_bound(w)):
            return WrappedInterval(WrappedInterval._mod_mul(a, c, w), WrappedInterval._mod_mul(b, d, w), no_of_bits=w)
        # case 2
        if msb_a == msb_b and msb_b == 1 and msb_c == msb_d and msb_d == 0 and \
                ((b*c - a*d) <= WrappedInterval._max_upper_bound(w)):
            return WrappedInterval(WrappedInterval._mod_mul(a, d, w), WrappedInterval._mod_mul(b, c, w), no_of_bits=w)
        # case 3
        if msb_a == msb_b and msb_b == 0 and msb_c == msb_d and msb_d == 1 and \
                ((a*d - b*c) <= WrappedInterval._max_upper_bound(w)):
            return WrappedInterval(WrappedInterval._mod_mul(b, c, w), WrappedInterval._mod_mul(a, d, w), no_of_bits=w)
        # otherwise
        return WrappedInterval._get_top(w)

    @staticmethod
    def _unsigned_mul(a, b, c, d, w):
        """
        Implementation of unsigned multiplication
        UnSign multiply the current interval with given interval
        Refer section 3.2 Analysing expression
        :param a: first lower bound
        :param b: first upper bound
        :param c: second lower bound
        :param d: second upper bound
        :param w: bit width
        :return: Interval representing result interval
        """

        # case 1
        if (b*d - a*c) <= WrappedInterval._max_upper_bound(w):
            return WrappedInterval(WrappedInterval._mod_mul(a, c, w), WrappedInterval._mod_mul(b, d, w), no_of_bits=w)
        # otherwise
        return WrappedInterval._get_top(w)

    @staticmethod
    def _unsigned_signed_mul(a, b, c, d, w):
        """
        Implementation of signed-unsigned multiplication
        UnSign multiply the current interval with given interval
        Refer section 3.2 Analysing expression
        :param a: first lower bound
        :param b: first upper bound
        :param c: second lower bound
        :param d: second upper bound
        :param w: bit width
        :return: Interval representing result interval
        """
        unsigned_res = WrappedInterval._unsigned_mul(a, b, c, d, w)
        signed_res = WrappedInterval._signed_mul(a, b, c, d, w)
        return unsigned_res.intersect(signed_res)

    @staticmethod
    def _truncate_num(num, k):
        """
        Truncate the given number to k bits
        :param num: Number to truncate
        :param k: Number of bits in result
        :return: Result of truncating the number to k bits
        """
        return num & WrappedInterval._max_upper_bound(k)

    @staticmethod
    def _arithmetic_right_shift(num, w, k):
        """
        Perform arithmetic shift of the given number by k bits
        :param num: number to be shifted
        :param w: Size of num in bits
        :param k: number of bits to shift
        :return: Number after shifting k bits
        """
        # convert the number into signed representation
        num = WrappedInterval._get_signed_repr(num, w)
        return num >> k

    def is_top(self):
        """
        This function returns if this wrapped interval is top
        :return: True if this is top or False if this is not
        """
        # Lower bound should be 0
        # Upper bound should be the maximum element
        return (self.lower_bound == 0) and \
               (self.upper_bound == WrappedInterval._max_upper_bound(self.no_of_bits))

    def is_bottom(self):
        """
        This function returns True if this WrappedInterval is Bottom else False
        :return: True if the wrapped interval is true else false
        """
        return self.is_bottom_flag

    def get_size(self):
        """
        Gets the size of the interval represented by this range
        Refer section 3.1
        :return: Size or number of elements in this interval
        """
        # case 1
        if self.is_bottom():
            return 0
        # case 2
        if self.is_top():
            return 1 << self.no_of_bits
        # case 3
        y_x = WrappedInterval._mod_sub(self.upper_bound, self.lower_bound, self.no_of_bits)
        return WrappedInterval._mod_add(y_x, 1, self.no_of_bits)

    def get_complement(self):
        """
        Return the complement of the interval
        Refer section 3.1
        :return:
        """
        # case 1
        if self.is_bottom():
            return WrappedInterval._get_top(self.no_of_bits)
        # case 2
        if self.is_top():
            return WrappedInterval._get_bottom(self.no_of_bits)
        # case 3
        y_plus_1 = WrappedInterval._mod_add(self.upper_bound, 1, self.no_of_bits)
        x_minus_1 = WrappedInterval._mod_sub(self.lower_bound, 1, self.no_of_bits)
        return WrappedInterval(y_plus_1, x_minus_1, self.no_of_bits)

    # Section 3.1 Ordering Wrapped Intervals
    def is_in_interval(self, target_number):
        """
        Check if target_number is in the range represented by this object.
        # Refer section 3.1
        :param target_number: number to be checked.
        :return: True if target_number is in this range else False
        """
        # case 0
        # if the number if more than max number representable by this range
        if target_number > WrappedInterval._max_upper_bound(self.no_of_bits):
            return False
        # case 1
        if self.is_top():
            return True
        # case 2
        if self.is_bottom():
            return False
        # case 3
        return WrappedInterval._less_than_a(target_number, self.upper_bound, self.lower_bound,
                                            self.no_of_bits)

    def is_interval_included(self, to_check_interval):
        """
        Check if to_check_interval is in interval represented by this object.
        Refer 1:8, 3.2 of paper:
            Interval analysis and machine arithmetic: Why signedness ignorance is bliss
        :param to_check_interval: Interval to check
        :return: True if to_check_interval is in this range else False
        """
        assert to_check_interval is not None, "Interval to check should be not None"
        # Case 1
        if self.is_top() or to_check_interval.is_bottom() or self == to_check_interval:
            return True
        # Case 2
        if to_check_interval.is_top() or self.is_bottom():
            return False
        # Case 3
        return (self.is_in_interval(to_check_interval.lower_bound)) and \
               (self.is_in_interval(to_check_interval.upper_bound)) and \
               ((not to_check_interval.is_in_interval(self.lower_bound)) or
                (not to_check_interval.is_in_interval(self.upper_bound)))

    def join(self, target_interval):
        """
        Join of 2-intervals (Pseudo-join operation)
        Join this interval with given interval
        Refer section 3.1
        :param target_interval: Interval containing both the intervals
        :return: Interval representing join of 2 intervals
        """
        assert self.no_of_bits == target_interval.no_of_bits, "Number of bits should be same for both operands"
        w = self.no_of_bits
        # we are using same names as in paper
        s = self
        t = target_interval
        # (a, b) = s
        a = self.lower_bound
        b = self.upper_bound
        # (c, d) = t
        c = t.lower_bound
        d = t.upper_bound
        # case 1
        if t.is_interval_included(s):
            return t.copy()
        # case 2
        if s.is_interval_included(t):
            return s.copy()
        # case 3
        if t.is_in_interval(a) and t.is_in_interval(b) and \
           s.is_in_interval(c) and s.is_in_interval(d):
            return WrappedInterval._get_top(w)
        # case 4
        if t.is_in_interval(b) and s.is_in_interval(c):
            return WrappedInterval(a, d, no_of_bits=w)
        # case 5
        if s.is_in_interval(d) and t.is_in_interval(a):
            return WrappedInterval(c, b, no_of_bits=w)
        # case 6
        b_c = WrappedInterval(b, c, no_of_bits=w)
        d_a = WrappedInterval(d, a, no_of_bits=w)
        if (b_c.get_size() < d_a.get_size()) or ((b_c.get_size() == d_a.get_size()) and a <= c):
            return WrappedInterval(a, d, no_of_bits=w)
        # otherwise
        return WrappedInterval(c, b, no_of_bits=w)

    def meet(self, target_interval):
        """
        Meet of 2 intervals (Pseudo meet operator)
        Perform meet of this interval with given interval
        Refer Section 3.1
        :param target_interval: interval to perform meet with
        :return: new Interval representing meet of the both intervals
        """
        s_compl = self.get_complement()
        t_compl = target_interval.get_complement()
        return s_compl.join(t_compl).get_complement()

    def intersect(self, target_interval):
        """
        Intersect the current interval with given interval and return the set of intervals
        Refer end of section 3.1, S n U
        :param target_interval: The target interval to intersect the current interval with
        :return: Set of intervals which are the result of intersection
        """
        assert self.no_of_bits == target_interval.no_of_bits, "Number of bits should be same for intervals to intersect"
        # using same variable names as in paper
        s = self
        t = target_interval
        w = self.no_of_bits
        # case 1
        if s.is_bottom() or t.is_bottom():
            return set()
        # case 2
        if s == t or s.is_top():
            return set([t.copy()])
        # case 3
        if t.is_top():
            return set([s.copy()])
        (a, b) = (s.lower_bound, s.upper_bound)
        (c, d) = (t.lower_bound, t.upper_bound)
        # case 4
        if t.is_in_interval(a) and t.is_in_interval(b) and s.is_in_interval(c) and s.is_in_interval(d):
            item1 = WrappedInterval(a, d, no_of_bits=w)
            item2 = WrappedInterval(b, c, no_of_bits=w)
            return set([item1, item2])
        # case 5
        if t.is_in_interval(a) and t.is_in_interval(b):
            return set([s.copy()])
        # case 6
        if s.is_in_interval(c) and s.is_in_interval(d):
            return set([t.copy()])
        # case 7
        if t.is_in_interval(a) and s.is_in_interval(d) and (not t.is_in_interval(b)) and (not s.is_in_interval(c)):
            item1 = WrappedInterval(a, d, no_of_bits=w)
            return set([item1])
        # case 8
        if t.is_in_interval(b) and s.is_in_interval(c) and (not t.is_in_interval(a)) and (not s.is_in_interval(d)):
            item1 = WrappedInterval(b, c, no_of_bits=w)
            return set([item1])
        # otherwise
        return set()

    # Addition and Subtraction

    def add(self, to_add):
        """
        Function to add an interval to the current interval
        Refer section 3.2 Analysing Expressions
        :param to_add: Target interval to add
        :return: Result of adding provided interval to this interval
        """
        assert to_add is not None, "Interval to add should not be None"
        result_bit_len = max(self.no_of_bits, to_add.no_of_bits)
        # case 1
        if self.is_bottom() or to_add.is_bottom():
            return WrappedInterval._get_bottom(result_bit_len)

        # case 2
        if (self.get_size() + to_add.get_size()) <= WrappedInterval._max_upper_bound(result_bit_len):
            # Get new lower bound; In paper: a +w b
            new_lower_bound = WrappedInterval._mod_add(self.lower_bound, to_add.lower_bound, result_bit_len)
            # Get new upper bound; In paper: b +w d
            new_upper_bound = WrappedInterval._mod_add(self.upper_bound, to_add.upper_bound, result_bit_len)
            return WrappedInterval(new_lower_bound, new_upper_bound, no_of_bits=result_bit_len)
        # case 3
        return WrappedInterval._get_top(result_bit_len)

    def subtract(self, to_sub):
        """
        Subtract the provided interval from the current interval
        Refer section 3.2 Analysing Expressions
        :param to_sub: Interval to subtract
        :return: Result of subtracting given interval from the current interval
        """
        assert to_sub is not None, "Interval to Subtract should not be None"
        result_bit_len = max(self.no_of_bits, to_sub.no_of_bits)
        # case 1
        if self.is_bottom() or to_sub.is_bottom():
            return WrappedInterval._get_bottom(result_bit_len)

        # case 2
        if (self.get_size() + to_sub.get_size()) <= WrappedInterval._max_upper_bound(result_bit_len):
            # Get new lower bound; In paper: a -w b
            new_lower_bound = WrappedInterval._mod_sub(self.lower_bound, to_sub.lower_bound, result_bit_len)
            # Get new upper bound; In paper: b -w d
            new_upper_bound = WrappedInterval._mod_sub(self.upper_bound, to_sub.upper_bound, result_bit_len)
            return WrappedInterval(new_lower_bound, new_upper_bound, no_of_bits=result_bit_len)
        # case 3
        return WrappedInterval._get_top(result_bit_len)

    def nsplit(self):
        """
        Split the interval at north pole
        Refer section 3.2 Analysing Expressions (nsplit)
        :return: Set containing resulting intervals after splitting at north pole
        """
        # case 1
        if self.is_bottom():
            return None
        north_pole = WrappedInterval._get_north_pole(self.no_of_bits)
        south_pole = WrappedInterval._get_south_pole(self.no_of_bits)
        # case 4
        if self.is_top():
            elem1 = WrappedInterval(south_pole.upper_bound, north_pole.lower_bound, no_of_bits=self.no_of_bits)
            elem2 = WrappedInterval(north_pole.upper_bound, south_pole.lower_bound, no_of_bits=self.no_of_bits)
            return [elem1, elem2]
        # case 2
        if not self.is_interval_included(north_pole):
            return [WrappedInterval(self.lower_bound, self.upper_bound, no_of_bits=self.no_of_bits)]
        else:  # case 3
            elem1 = WrappedInterval(self.lower_bound, north_pole.lower_bound, no_of_bits=self.no_of_bits)
            elem2 = WrappedInterval(north_pole.upper_bound, self.upper_bound, no_of_bits=self.no_of_bits)
            return [elem1, elem2]

    def ssplit(self):
        """
        Split this interval at south pole
        Refer section 3.2 Analysing Expressions (ssplit)
        :return: Set containing resulting intervals after splitting at south pole
        """
        # case 1
        if self.is_bottom():
            return None
        north_pole = WrappedInterval._get_north_pole(self.no_of_bits)
        south_pole = WrappedInterval._get_south_pole(self.no_of_bits)
        # case 4
        if self.is_top():
            elem1 = WrappedInterval(south_pole.upper_bound, north_pole.lower_bound, no_of_bits=self.no_of_bits)
            elem2 = WrappedInterval(north_pole.upper_bound, south_pole.lower_bound, no_of_bits=self.no_of_bits)
            return [elem1, elem2]
        # case 2
        if not self.is_interval_included(south_pole):
            return [WrappedInterval(self.lower_bound, self.upper_bound, no_of_bits=self.no_of_bits)]
        else:  # case 3
            elem1 = WrappedInterval(self.lower_bound, south_pole.lower_bound, no_of_bits=self.no_of_bits)
            elem2 = WrappedInterval(south_pole.upper_bound, self.upper_bound, no_of_bits=self.no_of_bits)
            return [elem1, elem2]

    def cut(self):
        """
        Sphere cut
        Refer section 3.2
        :return: Set containing the resulting intervals
        """
        to_ret = set()
        for u in self.nsplit():
            to_ret.update(set(u.ssplit()))
        return to_ret

    def copy(self):
        """
        Copy the given interval
        :return: Copy of this interval
        """
        return WrappedInterval(self.lower_bound, self.upper_bound, no_of_bits=self.no_of_bits,
                               is_bottom_flag=self.is_bottom())

    # Multiplication and Division

    def multiply(self, operand_interval):
        """
        Multiply this interval with the given interval
        Refer section 3.2
        :param operand_interval: Interval to be multiplied with
        :return: Resulting interval after multiplication
        """
        assert self.no_of_bits == operand_interval.no_of_bits, "Number of bits have to be same for both operands of " \
                                                               "multiplication"
        all_resulting_intervals = set()
        # using same variable names as in paper
        s = self
        t = operand_interval
        w = s.no_of_bits
        for u in s.cut():
            for v in t.cut():
                (a, b) = (u.lower_bound, u.upper_bound)
                (c, d) = (v.lower_bound, v.upper_bound)
                for m in WrappedInterval._unsigned_signed_mul(a, b, c, d, w):
                    all_resulting_intervals.add(m)

        return WrappedInterval._least_upper_bound(list(all_resulting_intervals))

    def unsigned_div(self, denominator_interval):
        """
        Perform unsigned division of the current interval with given interval
        Refer 1:15 of paper:
        Interval analysis and machine arithmetic: Why signedness ignorance is bliss
        :param denominator_interval: Denominator interval to be used
        :return: Resulting interval containing all results.
        """
        all_resulting_intervals = set()
        # using same variable names as in paper
        s = self
        t = denominator_interval
        w = s.no_of_bits
        for u in s.ssplit():
            for v in t.ssplit():
                (a, b) = (u.lower_bound, u.upper_bound)
                (c, d) = (v.lower_bound, v.upper_bound)
                # v \ (0, 0)
                if c != 0 and d != 0:
                    curr_result = WrappedInterval._mod_u_range_div(a, b, c, d, w)
                    all_resulting_intervals.add(curr_result)

        return WrappedInterval._least_upper_bound(list(all_resulting_intervals))

    def signed_div(self, denominator_interval):
        """
        Perform signed division of the current interval with given interval
        Refer 1:15 of paper:
        Interval analysis and machine arithmetic: Why signedness ignorance is bliss
        :param denominator_interval: Denominator interval to be used
        :return: Resulting interval containing all results.
        """
        all_resulting_intervals = set()
        # using same variable names as in paper
        s = self
        t = denominator_interval
        w = s.no_of_bits
        for u in s.cut():
            for v in t.cut():
                (a, b) = (u.lower_bound, u.upper_bound)
                (c, d) = (v.lower_bound, v.upper_bound)
                # v \ (0, 0)
                if c != 0 and d != 0:
                    curr_result = WrappedInterval._mod_s_range_div(a, b, c, d, w)
                    all_resulting_intervals.add(curr_result)

        return WrappedInterval._least_upper_bound(list(all_resulting_intervals))

    # Bitwise Operations

    def bitwise_or(self, operand_interval):
        """
        Perform bitwise OR of this interval with provided interval
        Refer section 3.2
        :param operand_interval: interval to OR with
        :return: Interval representing the range of result
        """
        assert self.no_of_bits == operand_interval.no_of_bits, "Number of bits should be same for OR operands"
        # Using same variables as in paper
        s = self
        t = operand_interval
        result_interval_set = set()
        for u in s.ssplit():
            for v in t.ssplit():
                w = u.no_of_bits
                # u |w v
                low_bound = WarrenMethods.min_or(u.lower_bound, u.upper_bound, v.lower_bound, v.upper_bound, w)
                upper_bound = WarrenMethods.max_or(u.lower_bound, u.upper_bound, v.lower_bound, v.upper_bound, w)
                new_interval = WrappedInterval(low_bound, upper_bound, no_of_bits=w)
                result_interval_set.add(new_interval)
        return WrappedInterval._least_upper_bound(list(result_interval_set))

    def bitwise_and(self, operand_interval):
        """
        Perform bitwise AND of this interval with provided interval
        Refer section 3.2
        :param operand_interval: interval to AND with
        :return: Interval representing the range of result
        """
        assert self.no_of_bits == operand_interval.no_of_bits, "Number of bits should be same for AND operands"
        # Using same variables as in paper
        s = self
        t = operand_interval
        result_interval_set = set()
        for u in s.ssplit():
            for v in t.ssplit():
                w = u.no_of_bits
                # u &w v
                low_bound = WarrenMethods.min_and(u.lower_bound, u.upper_bound, v.lower_bound, v.upper_bound, w)
                upper_bound = WarrenMethods.max_and(u.lower_bound, u.upper_bound, v.lower_bound, v.upper_bound, w)
                new_interval = WrappedInterval(low_bound, upper_bound, no_of_bits=w)
                result_interval_set.add(new_interval)
        return WrappedInterval._least_upper_bound(list(result_interval_set))

    def bitwise_xor(self, operand_interval):
        """
        Perform bitwise XOR of this interval with provided interval
        Refer section 3.2
        :param operand_interval: interval to XOR with
        :return: Interval representing the range of result
        """
        assert self.no_of_bits == operand_interval.no_of_bits, "Number of bits should be same for XOR operands"
        # Using same variables as in paper
        s = self
        t = operand_interval
        result_interval_set = set()
        for u in s.ssplit():
            for v in t.ssplit():
                w = u.no_of_bits
                # u |w v
                low_bound = WarrenMethods.min_xor(u.lower_bound, u.upper_bound, v.lower_bound, v.upper_bound, w)
                upper_bound = WarrenMethods.max_xor(u.lower_bound, u.upper_bound, v.lower_bound, v.upper_bound, w)
                new_interval = WrappedInterval(low_bound, upper_bound, no_of_bits=w)
                result_interval_set.add(new_interval)
        return WrappedInterval._least_upper_bound(list(result_interval_set))

    # Extension operations: Zero Extend and Sign Extend

    def zero_extend(self, k):
        """
        Zero extend the current interval by given number of bits
        Refer section 3.2
        :param k: Number of bits to extend. New size would be: current size + k
        :return: New interval whose size is current interval size + k
        """
        assert k > 0, "Number of bits to extend should be greater than zero"
        # Number of bits in result
        new_bit_length = self.no_of_bits + k
        s = self
        result_interval_set = set()
        for t in s.ssplit():
            (a, b) = (t.lower_bound, t.upper_bound)
            curr_result = WrappedInterval(a, b, no_of_bits=new_bit_length)
            result_interval_set.add(curr_result)
        return WrappedInterval._least_upper_bound(list(result_interval_set))

    def sign_extend(self, k):
        """
        Sign extend the current interval by given number of bits
        Refer section 3.2
        :param k: Number of bits to extend. New size would be: current size + k
        :return: New interval whose size is current interval size + k
        """
        assert k > 0, "Number of bits to extend should be greater than zero"
        # Number of bits in result
        new_bit_length = self.no_of_bits + k
        # value of length new_bit_length bits where most significant k bits are ones.
        msb_flag = ((1 << k) - 1) << self.no_of_bits
        s = self
        result_interval_set = set()
        for t in s.nsplit():
            (a, b) = (t.lower_bound, t.upper_bound)
            curr_result = WrappedInterval(msb_flag | a, msb_flag | b, no_of_bits=new_bit_length)
            result_interval_set.add(curr_result)
        return WrappedInterval._least_upper_bound(list(result_interval_set))

    # Bit shifting operations

    def truncate_range(self, target_bits):
        """
        Truncate this range to target bits
        Refer section 3.2 from paper
        :param target_bits: Number of bits in the result
        :return: Range truncated to target_bits
            Result will be of length target_bits length
        """

        assert target_bits < self.no_of_bits, "Target number of bits for truncate " \
                                              "should be less than current number of bits"
        # Same variable names as in paper
        s = self
        w = self.no_of_bits
        k = target_bits
        # case 1
        if self.is_bottom():
            return WrappedInterval._get_bottom(k)

        (a, b) = (s.lower_bound, s.upper_bound)
        a_rshift_k = WrappedInterval._arithmetic_right_shift(a, w, k)
        b_rshift_k = WrappedInterval._arithmetic_right_shift(b, w, k)
        a_trunc_k = WrappedInterval._truncate_num(a, k)
        b_trunc_k = WrappedInterval._truncate_num(b, k)
        # case 2
        if a_rshift_k == b_rshift_k and a_trunc_k <= b_trunc_k:
            return WrappedInterval(a_trunc_k, b_trunc_k, no_of_bits=k)
        # case 3
        if WrappedInterval._mod_equals(a_rshift_k + 1, b_rshift_k, w) and not (a_trunc_k <= b_trunc_k):
            return WrappedInterval(a_trunc_k, b_trunc_k, no_of_bits=k)
        # otherwise
        return WrappedInterval._get_top(k)

    def left_shift(self, target_bits):
        """
        Perform left shift of this interval by target bits
        Refer Section 3.2
        :param target_bits: number of bits to shift
        :return: Resulting interval after performing shift
        """
        # Same variable names as in paper
        s = self
        k = target_bits
        (a, b) = (s.lower_bound, s.upper_bound)
        w = self.no_of_bits
        # case 1
        if self.is_bottom():
            return WrappedInterval._get_bottom(w)
        # case 2
        trunc_result = s.truncate_range(w - k)
        if trunc_result.lower_bound == a and trunc_result.upper_bound == b:
            return WrappedInterval(a << k, b << k, no_of_bits=w)

        # otherwise
        # 1...w-k..110..k..0
        msb_w_k = ((1 << (w - k)) - 1) << k
        return WrappedInterval(0, msb_w_k, no_of_bits=w)

    def logical_right_shift(self, target_bits):
        """
        Perform logical right shift of this interval by target bits
        Refer Section 3.2
        :param target_bits: number of bits to shift
        :return: Resulting interval after performing shift
        """
        # Same variable names as in paper
        s = self
        k = target_bits
        (a, b) = (s.lower_bound, s.upper_bound)
        w = self.no_of_bits
        # case 1
        if self.is_bottom():
            return WrappedInterval._get_bottom(w)
        # case 2
        # 00...k..0011..w-k.11
        lsb_w_k = ((1 << (w - k)) - 1)
        sp = WrappedInterval._get_south_pole(w)
        if s.is_interval_included(sp):
            return WrappedInterval(0, lsb_w_k, no_of_bits=w)
        # otherwise
        return WrappedInterval(a >> k, b >> k, no_of_bits=w)

    def arithmetic_right_shift(self, target_bits):
        """
        Perform arithmetic right shift of this interval by target bits
        Refer Section 3.2
        :param target_bits: number of bits to shift
        :return: Resulting interval after performing shift
        """
        # Same variable names as in paper
        s = self
        k = target_bits
        (a, b) = (s.lower_bound, s.upper_bound)
        w = self.no_of_bits
        # case 1
        if self.is_bottom():
            return WrappedInterval._get_bottom(w)
        # case 2
        msb_k = ((1 << k) - 1) << (w - k)
        # 00...k..0011..w-k.11
        lsb_w_k = ((1 << (w - k)) - 1)
        np = WrappedInterval._get_north_pole(w)
        if s.is_interval_included(np):
            return WrappedInterval(msb_k, lsb_w_k, no_of_bits=w)
        # otherwise
        return WrappedInterval(WrappedInterval._arithmetic_right_shift(a, w, k),
                               WrappedInterval._arithmetic_right_shift(b, w, k), no_of_bits=w)

    def __hash__(self):
        """
        Hash of this interval.
        :return: integer representing hash of this interval
        """
        return hash((self.lower_bound, self.upper_bound, self.no_of_bits, self.is_bottom()))

    def __eq__(self, other):
        """
        Function to check equality of 2 intervals
        :param other: interval to check against
        :return: True if intervals are equal else false
        """
        if isinstance(other, WrappedInterval):
            return self.lower_bound == other.lower_bound and \
                   self.upper_bound == other.upper_bound and \
                   self.no_of_bits == other.no_of_bits and \
                   self.is_bottom() == other.is_bottom()
        return False
