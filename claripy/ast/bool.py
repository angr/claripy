from .base import Base, I
from ..operations import op

class Bool(Base):
    @staticmethod
    def _from_bool(like, val):
        return BoolI(like._claripy, val)

Bool.__eq__ = op('__eq__', (Bool, Bool), Bool)
Bool.__ne__ = op('__ne__', (Bool, Bool), Bool)

class BoolI(I, Bool):
    pass
