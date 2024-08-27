from __future__ import annotations

from contextlib import suppress

from claripy import backends
from claripy.errors import BackendError


class EagerResolutionMixin:
    """EagerResolutionMixin is a mixin that overrides _concrete_value to add
    eager evaluation."""

    def _concrete_value(self, e):
        r = super()._concrete_value(e)
        if r is not None:
            return r

        for b in backends._eager_backends:
            with suppress(BackendError):
                return b.eval(e, 1)[0]

        return None
