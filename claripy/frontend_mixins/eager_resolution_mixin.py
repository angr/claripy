class EagerResolutionMixin(object):
    def _concrete_value(self, e):
        r = super(EagerResolutionMixin, self)._concrete_value(e)
        if r is not None:
            return r

        for b in backends._eager_backends:
            try:
                return b.eval(e, 1)[0]
            except BackendError:
                pass

        return None
    _concrete_constraint = _concrete_value

from .. import backends
from ..errors import BackendError
