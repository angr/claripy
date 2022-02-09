__all__ = ["BigInt"]

from .claricpp import *
from .expr import Expr
from enum import Enum
from typing import Optional

# TODO: deal with destruction / freeing memory
# TODO: slots!


class BigInt:
    """
    Wrap claricpp BigInt methods
    """
    class Mode(Enum):
        """
        An enum which notes how python ints should be / are stored in C
        """
        Str: int = claricpp.ClaricppBimStr
        Int: int = claricpp.ClaricppBimInt

    def mode(self, mode_: Optional[Mode]=None):
        """
        If mode_ is None, returns the current mode
        If mode_ is a Mode, sets the mode then returns the old mode
        """
        if mode_ is None:
            return claricpp.big_int_mode_get()
        else:
            return claricpp.big_int_mode_set(mode_.value)

class Backend:
    """
    The public claripy Backend base class
    """

    def __init__(self, raw):
        self._raw = raw

