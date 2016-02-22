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

    def __init__(self, lower_bound, upper_bound, no_of_bits=32):
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

    def is_in_interval(self, target_number):
        """
        Check if target_number is in the range represented by this object.
        # Refer section 3.1
        :param target_number: number to be checked.
        :return: True if target_number is in this range else False
        """
        # case 1
        if self.is_top():
            return True
        # case 2
        # Ignore Bottom case
        # case 3
        return WrappedInterval._less_than_a(target_number, self.upper_bound, self.lower_bound, self.no_of_bits)