from __future__ import annotations

from claripy import operations
from claripy.ast.base import Base


class Set(Base):
    pass


class BoolSet(Set):
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


# Primitive operations


def SI(bits: int, lb: int, ub: int, stride: int) -> BVSet:
    return BVSet(
        "BVSet",
        bits,
        frozenset(
            (lb, ub, stride),
        ),
    )


def Singleton(bits: int, value: int) -> BVSet:
    return SI(bits, value, value, 1)


def EmptySet(bits: int) -> BVSet:
    return BVSet("BVSet", bits, frozenset())


def FullSet(bits: int) -> BVSet:
    return SI(bits, 0, 2**bits - 1, 1)


# Set operations

Union = operations.op("BVSetUnion", (BVSet, BVSet), BVSet)
Intersection = operations.op("BVSetIntersection", (BVSet, BVSet), BVSet)
Widen = operations.op("BVSetWiden", (BVSet, BVSet), BVSet)

# Arithmetic operations
BVSetAdd = operations.op("BVSetAdd", (BVSet, BVSet), BVSet)
BVSetSub = operations.op("BVSetSub", (BVSet, BVSet), BVSet)
BVSetMul = operations.op("BVSetMul", (BVSet, BVSet), BVSet)
BVSetMod = operations.op("BVSetMod", (BVSet, BVSet), BVSet)

# Bitwise operations

BVSetAnd = operations.op("BVSetAnd", (BVSet, BVSet), BVSet)
BVSetOr = operations.op("BVSetOr", (BVSet, BVSet), BVSet)
BVSetXor = operations.op("BVSetXor", (BVSet, BVSet), BVSet)
BVSetRotateLeft = operations.op("BVSetRotateLeft", (BVSet, int), BVSet)
BVSetRotateRight = operations.op("BVSetRotateRight", (BVSet, int), BVSet)
BVSetLShR = operations.op("BVSetLShR", (BVSet, int), BVSet)

# Comparison operations

BVSetUGT = operations.op("BVSetUGT", (BVSet, BVSet), BoolSet)
BVSetUGE = operations.op("BVSetUGE", (BVSet, BVSet), BoolSet)
BVSetULT = operations.op("BVSetULT", (BVSet, BVSet), BoolSet)
BVSetULE = operations.op("BVSetULE", (BVSet, BVSet), BoolSet)
BVSetSGT = operations.op("BVSetSGT", (BVSet, BVSet), BoolSet)
BVSetSGE = operations.op("BVSetSGE", (BVSet, BVSet), BoolSet)
BVSetSLT = operations.op("BVSetSLT", (BVSet, BVSet), BoolSet)
BVSetSLE = operations.op("BVSetSLE", (BVSet, BVSet), BoolSet)

# Concat and Extract

BVSetConcat = operations.op("BVSetConcat", (BVSet, BVSet), BVSet)
BVSetExtract = operations.op("BVSetExtract", (int, int, BVSet), BVSet)
BVSetZeroExt = operations.op("BVSetZeroExt", (BVSet, int), BVSet)
BVSetSignExt = operations.op("BVSetSignExt", (BVSet, int), BVSet)

# If-Then-Else

BVSetIf = operations.op("BVSetIf", (BoolSet, BVSet, BVSet), BVSet)

# Reverse

BVSetReverse = operations.op("BVSetReverse", (BVSet,), BVSet)
