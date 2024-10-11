from __future__ import annotations

from claripy.annotation import RegionAnnotation
from claripy.ast.base import Base
from claripy.operations import length_same_check, op
from claripy.vsa_simplifications import simplify_bvset


class Set(Base):
    """Base class for set types. Do not use directly."""


class BoolSet(Set):
    """Set of boolean values. args[0] is if the set contains True, args[1] is if
    the set contains False. Since this type is fairly simple, it is implemented
    directly, all ops are immediate."""

    @staticmethod
    def true() -> BoolSet:
        return BoolSet("BoolSet", True, False)

    @staticmethod
    def false() -> BoolSet:
        return BoolSet("BoolSet", False, True)

    @staticmethod
    def empty() -> BoolSet:
        return BoolSet("BoolSet", False, False)

    @staticmethod
    def full() -> BoolSet:
        return BoolSet("BoolSet", True, True)

    def __and__(self, other: BoolSet | bool) -> BoolSet:
        if isinstance(other, BoolSet):
            return BoolSet(self.op, self.args[0] & other.args[0], self.args[1] & other.args[1])
        return BoolSet(self.op, self.args[0] & other, self.args[1] & other)

    def __rand__(self, other: BoolSet | bool) -> BoolSet:
        return self.__and__(other)

    def __or__(self, other: BoolSet | bool) -> BoolSet:
        if isinstance(other, BoolSet):
            return BoolSet(self.op, self.args[0] | other.args[0], self.args[1] | other.args[1])
        return BoolSet(self.op, self.args[0] | other, self.args[1] | other)

    def __ror__(self, other: BoolSet | bool) -> BoolSet:
        return self.__or__(other)

    def __contains__(self, item: bool) -> bool:
        return self.args[0] if item else self.args[1]


class BVSet(Set):
    """Set of bitvector values. For the BVSet op, args[0] is a set of strided
    intervals. Each strided interval is a tuple of (lower bound, upper bound,
    stride)."""

    def union(self, other: BVSet) -> BVSet:
        return Union(self, other)

    def intersection(self, other: BVSet) -> BVSet:
        return Intersection(self, other)

    def widen(self, other: BVSet) -> BVSet:
        return Widen(self, other)

    def __add__(self, other: BVSet) -> BVSet:
        return BVSetAdd(self, other)

    def __radd__(self, other: BVSet) -> BVSet:
        return BVSetAdd(other, self)

    def __sub__(self, other: BVSet) -> BVSet:
        return BVSetSub(self, other)

    def __rsub__(self, other: BVSet) -> BVSet:
        return BVSetSub(other, self)

    def __mul__(self, other: BVSet) -> BVSet:
        return BVSetMul(self, other)

    def __rmul__(self, other: BVSet) -> BVSet:
        return BVSetMul(other, self)

    def __mod__(self, other: BVSet) -> BVSet:
        return BVSetMod(self, other)

    def __rmod__(self, other: BVSet) -> BVSet:
        return BVSetMod(other, self)

    def __and__(self, other: BVSet) -> BVSet:
        return BVSetAnd(self, other)

    def __rand__(self, other: BVSet) -> BVSet:
        return BVSetAnd(other, self)

    def __or__(self, other: BVSet) -> BVSet:
        return BVSetOr(self, other)

    def __ror__(self, other: BVSet) -> BVSet:
        return BVSetOr(other, self)

    def __xor__(self, other: BVSet) -> BVSet:
        return BVSetXor(self, other)

    def __rxor__(self, other: BVSet) -> BVSet:
        return BVSetXor(other, self)

    def __lshift__(self, other: int) -> BVSet:
        return BVSetRotateLeft(self, other)

    def __rlshift__(self, other: int) -> BVSet:
        return BVSetRotateLeft(self, other)

    def __rshift__(self, other: int) -> BVSet:
        return BVSetRotateRight(self, other)

    def __rrshift__(self, other: int) -> BVSet:
        return BVSetRotateRight(other, self)

    def __gt__(self, other: BVSet) -> BoolSet:
        return BVSetUGT(self, other)

    def __ge__(self, other: BVSet) -> BoolSet:
        return BVSetUGE(self, other)

    def __lt__(self, other: BVSet) -> BoolSet:
        return BVSetULT(self, other)

    def __le__(self, other: BVSet) -> BoolSet:
        return BVSetULE(self, other)

    def __eq__(self, other: BVSet) -> BoolSet:
        return BVSetUGE(self, other) & BVSetULE(self, other)

    def __ne__(self, other: BVSet) -> BoolSet:
        return BVSetUGT(self, other) | BVSetULT(self, other)

    @property
    def singlevalued(self) -> bool:
        return self.cardinality == 1

    @property
    def multivalued(self) -> bool:
        return self.cardinality > 1

    @property
    def cardinality(self) -> int:
        if self.op == "BVSet":
            if self.args[0] == frozenset():
                return 0
            if len(self.args[0]) == 1:
                si = next(iter(self.args[0]))
                return (si[1] - si[0] + 1) // si[2]
            # TODO: Handle case where there are multiple SI. We can't just sum
            # the individual cardinalities because they might overlap.
            raise NotImplementedError("TODO")
        return simplify_bvset(self).cardinality


# Primitive operations


def SI(bits: int, lb: int, ub: int, stride: int) -> BVSet:
    """Creates a BVSet representing a single interval."""

    return BVSet(
        "BVSet",
        (
            frozenset(
                (lb, ub, stride),
            ),
        ),
        length=bits,
    )


def Singleton(value: int, bits: int) -> BVSet:
    """Creates a BVSet representing a single value."""

    if isinstance(value, bytes | bytearray | memoryview):
        value = int.from_bytes(value, "big")

    return SI(bits, value, value, 1)


def EmptySet(bits: int) -> BVSet:
    """Creates an empty BVSet."""

    return BVSet("BVSet", frozenset(), length=bits)


def FullSet(bits: int) -> BVSet:
    """Creates a BVSet representing the full set of values."""

    return SI(bits, 0, 2**bits - 1, 1)


def ValueSet(bvset: BVSet, region_id: str = "global", base_addr: int = 0) -> BVSet:
    return bvset.annotate(RegionAnnotation(region_id, base_addr, 0))


# Set operations

Union = op("BVSetUnion", (BVSet, BVSet), BVSet, extra_check=length_same_check)
Intersection = op("BVSetIntersection", (BVSet, BVSet), BVSet, extra_check=length_same_check)
Widen = op("BVSetWiden", (BVSet, BVSet), BVSet, extra_check=length_same_check)

# Arithmetic operations
BVSetAdd = op("BVSetAdd", (BVSet, BVSet), BVSet, extra_check=length_same_check)
BVSetSub = op("BVSetSub", (BVSet, BVSet), BVSet, extra_check=length_same_check)
BVSetMul = op("BVSetMul", (BVSet, BVSet), BVSet, extra_check=length_same_check)
BVSetMod = op("BVSetMod", (BVSet, BVSet), BVSet, extra_check=length_same_check)

# Bitwise operations

BVSetAnd = op("BVSetAnd", (BVSet, BVSet), BVSet, extra_check=length_same_check)
BVSetOr = op("BVSetOr", (BVSet, BVSet), BVSet, extra_check=length_same_check)
BVSetXor = op("BVSetXor", (BVSet, BVSet), BVSet, extra_check=length_same_check)
BVSetRotateLeft = op("BVSetRotateLeft", (BVSet, int), BVSet)
BVSetRotateRight = op("BVSetRotateRight", (BVSet, int), BVSet)
BVSetLShR = op("BVSetLShR", (BVSet, int), BVSet)

# Comparison operations

BVSetUGT = op("BVSetUGT", (BVSet, BVSet), BoolSet, extra_check=length_same_check)
BVSetUGE = op("BVSetUGE", (BVSet, BVSet), BoolSet, extra_check=length_same_check)
BVSetULT = op("BVSetULT", (BVSet, BVSet), BoolSet, extra_check=length_same_check)
BVSetULE = op("BVSetULE", (BVSet, BVSet), BoolSet, extra_check=length_same_check)
BVSetSGT = op("BVSetSGT", (BVSet, BVSet), BoolSet, extra_check=length_same_check)
BVSetSGE = op("BVSetSGE", (BVSet, BVSet), BoolSet, extra_check=length_same_check)
BVSetSLT = op("BVSetSLT", (BVSet, BVSet), BoolSet, extra_check=length_same_check)
BVSetSLE = op("BVSetSLE", (BVSet, BVSet), BoolSet, extra_check=length_same_check)

# Concat and Extract

BVSetConcat = op("BVSetConcat", (BVSet, BVSet), BVSet, extra_check=length_same_check)
BVSetExtract = op("BVSetExtract", (int, int, BVSet), BVSet)
BVSetZeroExt = op("BVSetZeroExt", (BVSet, int), BVSet)
BVSetSignExt = op("BVSetSignExt", (BVSet, int), BVSet)

# If-Then-Else

BVSetIf = op("BVSetIf", (BoolSet, BVSet, BVSet), BVSet, extra_check=lambda _, t, e: length_same_check(t, e))

# Reverse

BVSetReverse = op("BVSetReverse", (BVSet,), BVSet)
