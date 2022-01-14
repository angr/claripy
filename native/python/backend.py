__all__ = ["BigIntMode", "Backend"]

from claricpp import *
from expr import Expr
from enum import Enum
from functools import cache, cached_property

# TODO: deal with destruction / freeing memory
# TODO: slots!


class BigIntMode(Enum):
    """
    An enum which notes how python ints should be / are stored in C
    """

    Str: int = claricpp.ClaricppBimStr
    Int: int = claricpp.ClaricppBimInt


class Backend:
    """
    The public claripy Backend base class
    """

    def __init__(self, raw):
        self._raw = raw

    @cached_property
    def name(self) -> str:
        return to_utf8(claricpp.claricpp_backend_name(self._raw))

    def handles(self, expr: Expr) -> bool:
        """
        Returns true if and only if the particular backend can handle expr
        """
        return bool(claricpp.claricpp_backend_handles(self._raw, expr.raw))

    def simplify(self, expr: Expr) -> Expr:
        """
        Returns the Expr resulting from simplifying expr with self._raw
        """
        return Expr(claricpp.claricpp_backend_simplify(self._raw, expr.raw))

    def downsize(self) -> None:
        """
        Free memory by clearing caches and such within the backend
        """
        claricpp.claricpp_backend_downsize(self._raw)

    def clear_persistent_data(self) -> None:
        """
        Clear's data which persists across invocations of downsize.
        Warning: Do *not* use this function unless you know what you are doing
        """
        claricpp.claricpp_backend_clear_persistent_data(self._raw)

    def get_big_int_mode(self) -> BigIntMode:
        """
        Get the BigIntMode this backend is using
        """
        return BigIntMode(claricpp.claricpp_backend_get_big_int_mode(self._raw))

    def set_big_int_mode(self, mode: BigIntMode) -> BigIntMode:
        """
        Set the BigIntMode this backend should use
        Returns the old BigIntMode the backend used
        """
        return BigIntMode(
            claricpp.claricpp_backend_set_big_int_mode(self._raw, mode.value)
        )
