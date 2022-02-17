__all__ = ["LazyPrim", "LazyArg", "Expr", "Bits"]

import claricpp_ffi.lib

from .claricpp import *
from .annotation_spav import *
from .annotation import *
from .op_names import cpp_to_py
from functools import lru_cache
from typing import List

# TODO: deal with destruction / freeing memory
# TODO: slots!


class LazyPrim:
    """
    Wraps a Claricpp Prim. The .prim value is lazily evaluated
    """

    def __init__(self, raw):
        self._raw = raw

    @property
    @lru_cache(maxsize=None)
    def value(self):
        """
        Returns the python arg generated from the Claricpp object raw
        """
        tp = self._raw.type
        prim = self._raw.data.prim
        # Primitive
        if tp == claricpp.ClaricppTypeEnumBool:
            return bool(prim.boolean)
        elif tp == claricpp.ClaricppTypeEnumStr:
            return to_utf8(prim.str)
        elif tp == claricpp.ClaricppTypeEnumFloat:
            return prim.flt
        elif tp == claricpp.ClaricppTypeEnumDouble:
            return prim.dbl
        elif tp == claricpp.ClaricppTypeEnumVS:
            raise NotImplementedError()  # TODO: implement
        elif tp == claricpp.ClaricppTypeEnumU8:
            return prim.u8
        elif tp == claricpp.ClaricppTypeEnumU16:
            return prim.u16
        elif tp == claricpp.ClaricppTypeEnumU32:
            return prim.u32
        elif tp == claricpp.ClaricppTypeEnumU64:
            return prim.u64
        # Invalid
        else:
            raise NotImplementedError("Unknown Arg type: " + str(tp))


class LazyArg:
    """
    Wraps a Claricpp Arg ( my_expr.arg(i) is of this type ). The .arg value is lazily evaluated
    """

    def __init__(self, raw):
        self._raw = raw

    @property
    @lru_cache(maxsize=None)
    def value(self):
        """
        Returns the python arg generated from the Claricpp object raw
        """
        tp = self._raw.type
        if tp == claricpp.ClaricppTypeEnumBigInt:
            return to_utf8(self._raw.data.big_int)
        elif tp == claricpp.ClaricppTypeEnumExpr:
            return Expr(self._raw.data.expr)
        elif tp == claricpp.ClaricppTypeEnumRM:
            return claricpp.RM(self._raw.data.rm)
        elif tp == claricpp.ClaricppTypeEnumWidth:
            return claricpp.Width(self._raw.data.width)
        else:
            return LazyPrim(self._raw).value


class ID:
    """
    Wrap an object
    """

    def __init__(self, o):
        self.value = o


class Expr:
    """
    The claripy API for a claricpp Expr Base
    """

    def __init__(self, expr):
        self._expr = expr

    @property
    @lru_cache(maxsize=None)
    def symbolic(self) -> bool:
        return bool(claricpp.claricpp_expr_symbolic(self._expr))

    @property
    def lazy_args(self) -> list[LazyArg]: # TODO: cache
        """
        Return the raw LazyArg's contained by self
        """
        c_arr = claricpp.claricpp_expr_args(self._expr)
        return [LazyArg(c_arr.arr[i]) for i in range(c_arr.len)]

    @property
    def args(self): # TODO: cache
        """
        Return the args contained by self
        """
        return [i.value for i in self.lazy_args]

    def __repr__(self) -> str:
        return to_utf8(claricpp.claricpp_expr_repr(self._expr))

    @property
    @lru_cache(maxsize=None)
    def _type_name(self) -> str:
        return to_utf8(claricpp.claricpp_expr_type_name(self._expr))

    @property
    @lru_cache(maxsize=None)
    def _op_name(self) -> str:
        return to_utf8(claricpp.claricpp_expr_op_name(self._expr))

    @property
    @lru_cache(maxsize=None)
    def hash(self):
        return claricpp.claricpp_expr_hash(self._expr)

    @property
    @lru_cache(maxsize=None)
    def op(self) -> str:
        on = self._op_name
        if on == "Literal" or on == "Symbol":
            return cpp_to_py[(self._type_name, on)]
        return cpp_to_py[on]

    @property
    @lru_cache(maxsize=None)
    def lazy_annotations(self) -> AnnotationSPAV:
        return AnnotationSPAV(claricpp.claricpp_expr_annotations(self._expr))

    @property
    @lru_cache(maxsize=None)
    def annotations(self) -> List[Annotation]:
        raw = claricpp.claricpp_annotation_spav_to_array(self.lazy_annotations.raw)
        ret = [Annotation(raw.arr[i]) for i in range(raw.len)]
        claricpp_ffi.lib.claricpp_free_array_annotation(ffi.addressof(raw))
        return tuple(ret)

    @property
    @lru_cache(maxsize=None)
    def raw(self):
        """
        Get the raw expr self holds
        Warning: Do not call this function unless you know what you are doing!
        """
        return self._expr

    def move_from(self, other):
        """
        Moves ownership of other._expr to self
        """
        if self is not other:
            self._expr = other._expr
            other._expr = None


class Bits(Expr):
    """
    The claripy API for a claricpp Expr Bits
    """

    def __init__(self, raw):
        super().__init__(raw)

    @property
    @lru_cache(maxsize=None)
    def length(self):
        return claricpp.claricpp_expr_bit_length(self._expr)

    @lru_cache(maxsize=None)
    def size(self):
        return self.length

    @lru_cache(maxsize=None)
    def __len__(self) -> int:
        return self.length
