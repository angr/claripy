"""
AST class representing a collection of bits of a specified length.
Meant to be subclassed, e.g. by BVV.
"""

from .base import Base

class Bits(Base):
    def size(self):
        """
        Returns the length of the Bits object.
        """
        return self.length

    __len__ = size
