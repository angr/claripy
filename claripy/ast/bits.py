from ..ast.base import Base

class Bits(Base):
    """
    A base class for AST types that can be stored as a series of bits. Currently, this is bitvectors and IEEE floats.

    :ivar length:       The length of this value in bits.
    """
    __slots__ = ['length']

    def __init__(self, *args, **kwargs):
        length = kwargs.pop('length', None)
        if length is None:
            raise ClaripyOperationError("length of Bits must not be None")

        self.length = length

    def make_like(self, op, args, **kwargs):
        if 'length' not in kwargs: kwargs['length'] = self.length
        return Base.make_like(self, op, args, **kwargs)

    def size(self):
        return self.length

    def _type_name(self):
        return self.__class__.__name__ + str(self.length)

    def raw_to_bv(self):
        """
        Converts this data's bit-pattern to a bitvector.
        """
        raise NotImplementedError

    def raw_to_fp(self):
        """
        Converts this data's bit-pattern to an IEEE float.
        """
        raise NotImplementedError

    @staticmethod
    def _check_replaceability(old, new):
        if old.size() != new.size():
            raise ClaripyOperationError('replacements must have matching sizes')

    __len__ = size


from ..errors import ClaripyOperationError
