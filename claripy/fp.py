import functools

from .errors import ClaripyOperationError
from .backend import BackendObject

def compare_sorts(f):
    @functools.wraps(f)
    def compare_guard(self, o):
        if self.sort != o.sort:
            raise TypeError("FPVs are differently-sorted ({} and {})".format(self.sort, o.sort))
        return f(self, o)

    return compare_guard

def normalize_types(f):
    @functools.wraps(f)
    def normalize_helper(self, o):
        if isinstance(o, float):
            o = FPV(o, self.sort)

        if not isinstance(self, FPV) or not isinstance(o, FPV):
            raise TypeError("must have two FPVs")

        return f(self, o)

    return normalize_helper

class FPV(BackendObject):
    __slots__ = ['sort', 'value']

    def __init__(self, value, sort):
        if not isinstance(value, float) or not isinstance(sort, tuple) or len(sort) != 2 or not isinstance(sort[0], int) or not isinstance(sort[1], int):
            raise ClaripyOperationError("FPV needs a sort (mantissa size, exponent size) and a float value")

        self.value = value
        self.sort = sort

    def __hash__(self):
        return hash((self.value, self.sort))

    def __getstate__(self):
        return (self.value, self.sort)

    def __setstate__(self, (value, sort)):
        self.value = value
        self.sort = sort

    @normalize_types
    @compare_sorts
    def __add__(self, o):
        return FPV(self.value + o.value, self.sort)

    @normalize_types
    @compare_sorts
    def __sub__(self, o):
        return FPV(self.value - o.value, self.sort)

    @normalize_types
    @compare_sorts
    def __mul__(self, o):
        return FPV(self.value * o.value, self.sort)

    @normalize_types
    @compare_sorts
    def __mod__(self, o):
        return FPV(self.value % o.value, self.sort)

    @normalize_types
    @compare_sorts
    def __div__(self, o):
        return FPV(self.value / o.value, self.sort)

    #
    # Reverse arithmetic stuff
    #

    @normalize_types
    @compare_sorts
    def __radd__(self, o):
        return FPV(o.value + self.value, self.sort)

    @normalize_types
    @compare_sorts
    def __rsub__(self, o):
        return FPV(o.value - self.value, self.sort)

    @normalize_types
    @compare_sorts
    def __rmul__(self, o):
        return FPV(o.value * self.value, self.sort)

    @normalize_types
    @compare_sorts
    def __rmod__(self, o):
        return FPV(o.value % self.value, self.sort)

    @normalize_types
    @compare_sorts
    def __rdiv__(self, o):
        return FPV(o.value / self.value, self.sort)

    #
    # Boolean stuff
    #

    @normalize_types
    @compare_sorts
    def __eq__(self, o):
        return self.value == o.value

    @normalize_types
    @compare_sorts
    def __ne__(self, o):
        return self.value != o.value

    @normalize_types
    @compare_sorts
    def __lt__(self, o):
        return self.value < o.value

    @normalize_types
    @compare_sorts
    def __gt__(self, o):
        return self.value > o.value

    @normalize_types
    @compare_sorts
    def __le__(self, o):
        return self.value <= o.value

    @normalize_types
    @compare_sorts
    def __ge__(self, o):
        return self.value >= o.value

    def __repr__(self):
        return 'FPV({:f}, {})'.format(self.value, self.sort)

SINGLE = (8, 24)
DOUBLE = (11, 53)
