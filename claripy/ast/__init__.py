# pylint:disable=redefined-outer-name
from typing import TYPE_CHECKING

# Mypy is severely confused by this delayed import trickery, but works if we just pretend that the import
# happens here already
if TYPE_CHECKING:
    from .bits import Bits
    from .bv import BV
    from .fp import FP
    from .bool import Bool, true, false
    from .base import Base
    from .strings import String
    from claripy import ops as all_operations
else:
    Bits = lambda *args, **kwargs: None
    BV = lambda *args, **kwargs: None
    FP = lambda *args, **kwargs: None
    Bool = lambda *args, **kwargs: None
    Base = lambda *args, **kwargs: None
    true = lambda *args, **kwargs: None
    false = lambda *args, **kwargs: None
    String = lambda *args, **kwargs: None
    all_operations = None


def _import():
    global Bits, BV, FP, Bool, Base, String, true, false, all_operations

    from .bits import Bits
    from .bv import BV
    from .fp import FP
    from .bool import Bool, true, false
    from .base import Base
    from .strings import String
    from claripy import ops as all_operations


__all__ = ("Bits", "BV", "FP", "Bool", "true", "false", "Base", "String", "all_operations")
