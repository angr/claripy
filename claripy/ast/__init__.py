Bits = None
BV = None
VS = None
FP = None
Bool = None
Int = None
Base = None

def _import():
    global Bits, BV, VS, FP, Bool, Int, Base

    from .bits import Bits
    from .bv import BV
    from .vs import VS
    from .fp import FP
    from .bool import Bool
    from .int import Int
    from ..ast_base import Base
