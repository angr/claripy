from .base import Base, I
from ..operations import op

class Bool(Base):
    @staticmethod
    def _from_bool(clrp, like, val):
        return BoolI(clrp, val)

Bool.__eq__ = op('__eq__', (Bool, Bool), Bool)
Bool.__ne__ = op('__ne__', (Bool, Bool), Bool)

class BoolI(I, Bool):
    pass
