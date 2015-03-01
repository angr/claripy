from .base import Base

class Bits(Base):
    __slots__ = ['length']

    def __init__(self, *args, **kwargs):
        length = kwargs.pop('length', None)
        if length is None:
            raise ClaripyOperationError("length of Bits must not be None")

        self.length = length

    def size(self):
        return self.length

    __len__ = size


from ..errors import ClaripyOperationError
