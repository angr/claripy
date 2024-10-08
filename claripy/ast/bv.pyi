from typing import overload

from claripy.backends.backend_concrete.bv import BVV as ConcreteBVV
from claripy.fp import RM, FSort

from .bits import Bits
from .bool import Bool
from .fp import FP

CoerceBV = int | "BV"

class BV(Bits):
    def chop(self, bits: int = 1) -> list[BV]: ...
    def __getitem__(self, rng: int | slice) -> BV: ...
    def get_byte(self, index: int) -> BV: ...
    def get_bytes(self, index: int, size: int) -> BV: ...
    def zero_extend(self, n: int) -> BV: ...
    def sign_extend(self, n: int) -> BV: ...
    def concat(self, *args: BV) -> BV: ...
    @staticmethod
    def _from_int(like, value: int) -> BV: ...
    @staticmethod
    def _from_Bool(like, value: Bool) -> BV: ...
    @staticmethod
    def _from_bytes(like, value: bytes) -> BV: ...
    @staticmethod
    def _from_str(like, value: str) -> BV: ...
    @staticmethod
    def _from_BVV(like, value: ConcreteBVV) -> BV: ...
    def val_to_fp(self, sort: FSort, signed: bool = True, rm: RM | None = None) -> FP: ...
    def raw_to_fp(self) -> FP: ...
    def raw_to_bv(self) -> BV: ...
    def to_bv(self) -> BV: ...
    def __add__(self, other: CoerceBV) -> BV: ...
    def __radd__(self, other: CoerceBV) -> BV: ...
    def __floordiv__(self, other: CoerceBV) -> BV: ...
    def __rfloordiv__(self, other: CoerceBV) -> BV: ...
    def __truediv__(self, other: CoerceBV) -> BV: ...
    def __rtruediv__(self, other: CoerceBV) -> BV: ...
    def __mul__(self, other: CoerceBV) -> BV: ...
    def __rmul__(self, other: CoerceBV) -> BV: ...
    def __sub__(self, other: CoerceBV) -> BV: ...
    def __rsub__(self, other: CoerceBV) -> BV: ...
    def __pow__(self, other: CoerceBV) -> BV: ...
    def __rpow__(self, other: CoerceBV) -> BV: ...
    def __mod__(self, other: CoerceBV) -> BV: ...
    def __rmod__(self, other: CoerceBV) -> BV: ...
    def SDiv(self, other: CoerceBV) -> BV: ...
    def SMod(self, other: CoerceBV) -> BV: ...
    def __or__(self, other: CoerceBV) -> BV: ...
    def __ror__(self, other: CoerceBV) -> BV: ...
    def __and__(self, other: CoerceBV) -> BV: ...
    def __rand__(self, other: CoerceBV) -> BV: ...
    def __xor__(self, other: CoerceBV) -> BV: ...
    def __rxor__(self, other: CoerceBV) -> BV: ...
    def __lshift__(self, other: CoerceBV) -> BV: ...
    def __rlshift__(self, other: CoerceBV) -> BV: ...
    def __rshift__(self, other: CoerceBV) -> BV: ...
    def __rrshift__(self, other: CoerceBV) -> BV: ...
    def LShR(self, other: CoerceBV) -> BV: ...
    def __neg__(self) -> BV: ...
    def __pos__(self) -> BV: ...
    def __abs__(self) -> BV: ...
    def __invert__(self) -> BV: ...
    def __eq__(self, other: CoerceBV) -> Bool: ...
    def __ne__(self, other: CoerceBV) -> Bool: ...
    def __ge__(self, other: CoerceBV) -> Bool: ...
    def __le__(self, other: CoerceBV) -> Bool: ...
    def __gt__(self, other: CoerceBV) -> Bool: ...
    def __lt__(self, other: CoerceBV) -> Bool: ...
    def SLT(self, other: CoerceBV) -> Bool: ...
    def SLE(self, other: CoerceBV) -> Bool: ...
    def SGT(self, other: CoerceBV) -> Bool: ...
    def SGE(self, other: CoerceBV) -> Bool: ...
    def ULT(self, other: CoerceBV) -> Bool: ...
    def ULE(self, other: CoerceBV) -> Bool: ...
    def UGT(self, other: CoerceBV) -> Bool: ...
    def UGE(self, other: CoerceBV) -> Bool: ...
    def Extract(self, start: int, end: int) -> BV: ...
    def Concat(self, other: BV) -> BV: ...
    @property
    def reversed(self) -> BV: ...

    # weh
    def union(self, other: BV) -> BV: ...
    def widen(self, other: BV) -> BV: ...
    def intersection(self, other: BV) -> BV: ...
    @property
    def concrete_value(self) -> int: ...
    def __hash__(self) -> int: ...

def BVS(name: str, size: int, **kwargs) -> BV: ...
@overload
def BVV(value: int, size: int = ..., **kwargs) -> BV: ...
@overload
def BVV(value: bytes, **kwargs) -> BV: ...
def SI(
    name: str | None = ...,
    bits: int = ...,
    lower_bound: int | None = ...,
    upper_bound: int | None = ...,
    stride: int | None = ...,
): ...
def TSI(bits, name: str | None = ..., uninitialized: bool = ..., explicit_name: bool | None = ...): ...
def ESI(bits, **kwargs): ...
def ValueSet(
    bits,
    region: str | None = ...,
    region_base_addr: int | None = ...,
    value: int | None = ...,
    name: str | None = ...,
    val: int | None = ...,
): ...

VS = ValueSet

def ULT(a: BV | int, b: BV | int) -> Bool: ...
def ULE(a: BV | int, b: BV | int) -> Bool: ...
def UGT(a: BV | int, b: BV | int) -> Bool: ...
def UGE(a: BV | int, b: BV | int) -> Bool: ...
def SLT(a: BV | int, b: BV | int) -> Bool: ...
def SLE(a: BV | int, b: BV | int) -> Bool: ...
def SGT(a: BV | int, b: BV | int) -> Bool: ...
def SGE(a: BV | int, b: BV | int) -> Bool: ...
def SDiv(a: BV | int, b: BV | int) -> BV: ...
def SMod(a: BV | int, b: BV | int) -> BV: ...
def LShR(a: BV | int, b: BV | int) -> BV: ...
def SignExt(a: int, b: BV | int) -> BV: ...
def ZeroExt(a: int, b: BV | int) -> BV: ...
def Extract(a: int, b: int, BV) -> BV: ...
def Concat(*a: BV) -> BV: ...
def RotateLeft(a: BV | int, b: BV | int) -> BV: ...
def RotateRight(a: BV | int, b: BV | int) -> BV: ...
def Reverse(a: BV | int) -> BV: ...
def union(a: BV | int, b: BV | int) -> BV: ...
def widen(a: BV | int, b: BV | int) -> BV: ...
def intersection(a: BV | int, b: BV | int) -> BV: ...
