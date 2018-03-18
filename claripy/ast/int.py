from ..ast.base import Base
from .. import operations
from .bool import Bool

class Int(Base):
    pass

Int.__eq__ = operations.op('__eq__', (Int, Int), Bool)
