from ..ast.base import Base


class Bits(Base):
    """
    A base class for AST types that can be stored as a series of bits. Currently, this is bitvectors and IEEE floats.

    :ivar length:       The length of this value in bits.
    """

    length: int

    def make_like(self, op, args, **kwargs):
        if "length" not in kwargs:
            kwargs["length"] = self.length
        return Base.make_like(self, op, args, **kwargs)

    def size(self):
        """
        :returns: The bit length of this AST
        """
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
            raise ClaripyOperationError("replacements must have matching sizes")

    __len__ = size


from ..errors import ClaripyOperationError
