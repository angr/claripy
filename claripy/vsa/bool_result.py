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

    def size(self):
        return None

    @staticmethod
    def is_maybe(o):
        if isinstance(o, Base):
            o = o.model

        return isinstance(o, MaybeResult)

    @staticmethod
    def has_true(o):
        if isinstance(o, Base):
            o = o.model

        return o is True or \
               (isinstance(o, BoolResult) and True in o.value) or \
               (isinstance(o, IfProxy) and (True in o.trueexpr.value or True in o.falseexpr.value))

    @staticmethod
    def has_false(o):
        if isinstance(o, Base):
            o = o.model

        return o is False or \
               (isinstance(o, BoolResult) and False in o.value) or \
               (isinstance(o, IfProxy) and (False in o.trueexpr.value or False in o.falseexpr.value))

    @staticmethod
    def is_true(o):
        if isinstance(o, Base):
            o = o.model

        return o is True or \
               (isinstance(o, TrueResult)) or \
               (isinstance(o, IfProxy) and (type(o.trueexpr) is TrueResult and type(o.falseexpr) is TrueResult))

    @staticmethod
    def is_false(o):
        if isinstance(o, Base):
            o = o.model

        return o is False or \
               (isinstance(o, FalseResult)) or \
               (isinstance(o, IfProxy) and (type(o.trueexpr) is FalseResult and type(o.falseexpr) is FalseResult))

class TrueResult(BoolResult):
    @property
    def value(self):
        return (True, )

    def __eq__(self, other):
        return isinstance(other, TrueResult)

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

    def __repr__(self):
        return '<True>'

class FalseResult(BoolResult):
    @property
    def value(self):
        return (False, )

    def __eq__(self, other):
        return isinstance(other, FalseResult)

    def __invert__(self):
        return TrueResult()

    def __and__(self, other):
        return FalseResult()

    def __or__(self, other):
        return other

    def __repr__(self):
        return '<False>'

class MaybeResult(BoolResult):
    @property
    def value(self):
        return (True, False)

    def __eq__(self, other):
        return isinstance(other, MaybeResult)

    def __invert__(self):
        return MaybeResult()

    def __and__(self, other):
        if BoolResult.is_false(other):
            return FalseResult()
        else:
            return MaybeResult()

    def __or__(self, other):
        if BoolResult.is_true(other):
            return TrueResult()
        else:
            return self

    def __repr__(self):
        if self._op is None:
            return '<Maybe>'
        else:
            return '<Maybe(%s, %s)>' % (self._op, self._args)



from ..errors import BackendError
from .ifproxy import IfProxy
from ..ast.base import Base
