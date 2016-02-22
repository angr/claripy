"""
Faithful reproduction of paper Signedness-agnostic program analysis: Precise integer bounds for low-level code
This is meant to serve as a base implementation of wrapped intervals.
Any use of wrapped intervals should reuse this.
"""


class WrappedInterval(object):
    """
        Class representing a wrapped interval.
        Refer paper: Signedness-agnostic program analysis: Precise integer bounds for low-level code
    """

    def __init__(self, lower_bound, upper_bound, no_of_bits=32, is_bottom=False):
        """
        Construct a new wrapped interval with provided lower and upper bounds.
        :return:
        """
        assert isinstance(lower_bound, int), "Provided Lower Bound is not integer. Expected Integer."
        assert isinstance(upper_bound, int), "Provided Upper Bound is not integer. Expected Integer."
        assert isinstance(no_of_bits, int), "No of bits is not integer. Expected Integer."

        self.lower_bound = lower_bound
        self.upper_bound = upper_bound
        self.no_of_bits = no_of_bits
        self.is_bottom = is_bottom

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
        return self.is_bottom

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
            return WrappedInterval(0, (1 << self.no_of_bits)-1, no_of_bits=self.no_of_bits)
        # case 2
        if self.is_top():
            return WrappedInterval(0, (1 << self.no_of_bits)-1, no_of_bits=self.no_of_bits, is_bottom=True)
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
        return WrappedInterval._less_than_a(target_number, self.upper_bound, self.lower_bound, self.no_of_bits)

    def is_interval_included(self, to_check_interval):
        """
        Check if to_check_interval is in interval represented by this object.
        Refer section 3.1
        :param to_check_interval: Interval to check
        :return: True if to_check_interval is in this range else False
        """
        assert to_check_interval is not None, "Interval to check should be not None"
        # Case 1
        if self.is_top() or to_check_interval.is_bottom():
            return True
        # Case 2
        if to_check_interval.is_top() or self.is_bottom():
            return False
        # Case 3
        return (self.is_in_interval(to_check_interval.lower_bound)) and \
               (self.is_in_interval(to_check_interval.upper_bound)) and \
               ((not to_check_interval.is_in_interval(self.lower_bound)) or
                (not to_check_interval.is_in_interval(self.upper_bound)))
