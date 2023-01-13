from ..backend_object import BackendObject


class BoolResult(BackendObject):
    def __init__(self, op=None, args=None):
        self._op = op
        self._args = args

    def value(self):
        raise NotImplementedError()

    def __len__(self):
        return BackendError()

    def __eq__(self, other):
        raise NotImplementedError()

    def __and__(self, other):
        raise NotImplementedError()

    def __invert__(self):
        raise NotImplementedError()

    def __or__(self, other):
        raise NotImplementedError()

    def identical(self, other):
        if self.value != other.value:
            return False
        if self._op != other._op:
            return False
        if self._args != other._args:
            return False
        return True

    def union(self, other):
        raise NotImplementedError()

    def size(self):  # pylint:disable=no-self-use
        return None

    @staticmethod
    def is_maybe(o):
        if isinstance(o, Base):
            raise ClaripyValueError("BoolResult can't handle AST objects directly")

        return isinstance(o, MaybeResult)

    @staticmethod
    def has_true(o):
        if isinstance(o, Base):
            raise ClaripyValueError("BoolResult can't handle AST objects directly")

        return o is True or (isinstance(o, BoolResult) and True in o.value)

    @staticmethod
    def has_false(o):
        if isinstance(o, Base):
            raise ClaripyValueError("BoolResult can't handle AST objects directly")

        return o is False or (isinstance(o, BoolResult) and False in o.value)

    @staticmethod
    def is_true(o):
        if isinstance(o, Base):
            raise ClaripyValueError("BoolResult can't handle AST objects directly")

        return o is True or (isinstance(o, TrueResult))

    @staticmethod
    def is_false(o):
        if isinstance(o, Base):
            raise ClaripyValueError("BoolResult can't handle AST objects directly")

        return o is False or (isinstance(o, FalseResult))


class TrueResult(BoolResult):
    cardinality = 1

    @property
    def value(self):
        return (True,)

    def identical(self, other):
        return isinstance(other, TrueResult)

    def __eq__(self, other):
        if isinstance(other, FalseResult):
            return FalseResult()
        elif isinstance(other, TrueResult):
            return TrueResult()
        else:
            return MaybeResult()

    def __invert__(self):
        return FalseResult()

    def __or__(self, other):
        return TrueResult()

    def __and__(self, other):
        if BoolResult.is_maybe(other):
            return MaybeResult()
        elif BoolResult.is_false(other):
            return FalseResult()
        else:
            return TrueResult()

    def union(self, other):
        if other is True or type(other) is TrueResult:
            return TrueResult()
        elif other is False or type(other) is FalseResult:
            return MaybeResult()
        elif type(other) is MaybeResult:
            return MaybeResult()
        else:
            return NotImplemented

    def __repr__(self):
        return "<True>"

    def __bool__(self):
        return True


class FalseResult(BoolResult):
    cardinality = 1

    @property
    def value(self):
        return (False,)

    def identical(self, other):
        return isinstance(other, FalseResult)

    def __eq__(self, other):
        if isinstance(other, FalseResult):
            return TrueResult()
        elif isinstance(other, TrueResult):
            return FalseResult()
        else:
            return MaybeResult()

    def __invert__(self):
        return TrueResult()

    def __and__(self, other):
        return FalseResult()

    def __or__(self, other):
        return other

    def __repr__(self):
        return "<False>"

    def union(self, other):
        if other is True or type(other) is TrueResult:
            return MaybeResult()
        elif other is False or type(other) is FalseResult:
            return FalseResult()
        elif type(other) is MaybeResult:
            return MaybeResult()
        else:
            return NotImplemented

    def __bool__(self):
        return False


class MaybeResult(BoolResult):
    cardinality = 2

    @property
    def value(self):
        return (True, False)

    def identical(self, other):
        return isinstance(other, MaybeResult)

    def __eq__(self, other):
        return MaybeResult()

    def __invert__(self):
        return MaybeResult()

    def __and__(self, other):
        if BoolResult.is_false(other):
            return FalseResult()
        else:
            return MaybeResult()

    def union(self, other):
        return MaybeResult()

    def __or__(self, other):
        if BoolResult.is_true(other):
            return TrueResult()
        else:
            return self

    def __repr__(self):
        if self._op is None:
            return "<Maybe>"
        else:
            return f"<Maybe({self._op}, {self._args})>"

    def __bool__(self):
        return False


from ..errors import BackendError, ClaripyValueError
from ..ast.base import Base
