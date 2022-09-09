import functools
import warnings # TODO: does angr roll its own? Do we hook this?

from . import module

from ..load import Load as BaseLoad, clari


class Load(BaseLoad):
    def __init__(self, *, debug_mode: bool = False):
        msg = "Use setup_clari.Setup instead of LegacySetup"
        warnings.warn(msg, DeprecationWarning)
        super().__init__(debug_mode=debug_mode)

    @staticmethod
    def _deprecated(func):
        @functools.wraps(func)
        def ret(*args, **kwargs):
            warnings.warn(f"{func.__name__} is deprecated.", category=DeprecationWarning)
            return func(*args, **kwargs)
        return ret

    def define_members(self):
        super().define_members()
        # Legacy members
        clari.Expr.BV.__truediv__ = self._deprecated(clari.Expr.BV.__floordiv__)
        clari.Legacy = module

__all__ = ("Load",)
