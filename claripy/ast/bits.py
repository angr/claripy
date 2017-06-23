"""
AST class representing a collection of bits of a specified length.
Meant to be subclassed, e.g. by BVV.
"""

from ..ast.base import Base

class Bits(Base):
    """
    AST class representing a collection of bits of a certain length.

    :param length: Length (number) of bits. Must not be None.
    """
    __slots__ = ['length']

    def __init__(self, *args, **kwargs):
        length = kwargs.pop('length', None)
        if length is None:
            raise ClaripyOperationError("length of Bits must not be None")

        self.length = length

    def make_like(self, *args, **kwargs):
        if 'length' not in kwargs: kwargs['length'] = self.length
        return Base.make_like(self, *args, **kwargs)

    def size(self):
        """
        Returns the length of the Bits object.
        """
        return self.length

    def _type_name(self):
        return self.__class__.__name__ + str(self.length)

    @staticmethod
    def _check_replaceability(old, new):
        if old.size() != new.size():
            raise ClaripyOperationError('replacements must have matching sizes')

    __len__ = size


from ..errors import ClaripyOperationError
