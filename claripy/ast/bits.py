from ..ast.base import Base

class Bits(Base):
    def size(self):
        return self.length

    __len__ = size
