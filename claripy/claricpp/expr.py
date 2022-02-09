__all__ = ["LazyPrim", "LazyArg", "Expr", "Bits"]

from .claricpp import *
from .annotation_spav import *
from functools import lru_cache

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
        # Primitive
        if tp == claricpp.ClaricppTypeEnumBool:
            return bool(self._raw.data.value.boolean)
        elif tp == claricpp.ClaricppTypeEnumStr:
            return to_utf8(self._raw.data.value.str)
        elif tp == claricpp.ClaricppTypeEnumFloat:
            return self._raw.data.value.flt
        elif tp == claricpp.ClaricppTypeEnumDouble:
            return self._raw.data.value.dbl
        elif tp == claricpp.ClaricppTypeEnumVS:
            raise NotImplementedError()  # TODO: implement
        elif tp == claricpp.ClaricppTypeEnumU8:
            return self._raw.data.value.u8
        elif tp == claricpp.ClaricppTypeEnumU16:
            return self._raw.data.value.u16
        elif tp == claricpp.ClaricppTypeEnumU32:
            return self._raw.data.value.u32
        elif tp == claricpp.ClaricppTypeEnumU64:
            return self._raw.data.value.u64
        # Invalid
        else:
            raise NotImplementedError("Unknown Arg type: " + str(self._raw.type))


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
            return claricpp.Prim(self._raw).value


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
    @lru_cache(maxsize=None)
    def lazy_args(self) -> list[LazyArg]:
        """
        Return the raw LazyArg's contained by self
        """
        c_arr = claricpp.claricpp_expr_args(self._expr)
        arr = c_arr.arr
        return [LazyArg(arr[i]) for i in range(c_arr.len)]

    @property
    @lru_cache(maxsize=None)
    def args(self):
        """
        Return the args contained by self
        """
        return [i.value for i in self.lazy_args]

    def __repr__(self) -> str:
        return to_utf8(claricpp.claricpp_expr_repr(self._expr))

    @property
    @lru_cache(maxsize=None)
    def type_name(self) -> str:
        return to_utf8(claricpp.claricpp_expr_type_name(self._expr))

    @property
    @lru_cache(maxsize=None)
    def op_name(self) -> str:
        return to_utf8(claricpp.claricpp_expr_op_name(self._expr))

    @property
    @lru_cache(maxsize=None)
    def annotations(self) -> AnnotationSPAV:
        return AnnotationSPAV(claricpp.claricpp_expr_annotations(self._expr))

    @property
    @lru_cache(maxsize=None)
    def raw(self):
        """
        Get the raw expr self holds
        Warning: Do not call this function unless you know what you are doing!
        """
        return self._expr


class Bits(Expr):
    """
    The claripy API for a claricpp Expr Bits
    """

    def __init__(self, raw):
        super().__init__(raw)

    @lru_cache(maxsize=None)
    def __len__(self) -> int:
        return claricpp.claricpp_expr_bit_length(self._expr)
