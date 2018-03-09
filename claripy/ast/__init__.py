#pylint:disable=redefined-outer-name
Bits = lambda *args, **kwargs: None
BV = lambda *args, **kwargs: None
VS = lambda *args, **kwargs: None
FP = lambda *args, **kwargs: None
Bool = lambda *args, **kwargs: None
Int = lambda *args, **kwargs: None
Base = lambda *args, **kwargs: None
true = lambda *args, **kwargs: None
false = lambda *args, **kwargs: None
String = lambda *args, **kwargs: None
all_operations = None

def _import():
    global Bits, BV, VS, FP, Bool, Int, Base, String, true, false, all_operations

    from .bits import Bits
    from .bv import BV
    from .vs import VS
    from .fp import FP
    from .bool import Bool, true, false
    from .int import Int
    from .base import Base
    from .strings import String
    from .. import ops as all_operations
