
class BoolResult(object):
    pass

    def value(self):
        raise NotImplementedError()

    def __len__(self):
        return BackendError()

    def size(self):
        return None

    @staticmethod
    def is_true(o):
        return isinstance(o, TrueResult)

    @staticmethod
    def is_false(o):
        return isinstance(o, FalseResult)

    @staticmethod
    def is_maybe(o):
        return isinstance(o, MaybeResult)

class TrueResult(BoolResult):
    @property
    def value(self):
        return (True, )

    def __eq__(self, other):
        return isinstance(other, TrueResult)

    def __invert__(self):
        return FalseResult()

    def __and__(self, other):
        if BoolResult.is_maybe(other):
            return MaybeResult()
        elif BoolResult.is_false(other):
            return FalseResult()
        else:
            return TrueResult()

    def __repr__(self):
        return 'True'

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

    def __repr__(self):
        return 'False'

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

    def __repr__(self):
        return 'Maybe'

from ..errors import BackendError