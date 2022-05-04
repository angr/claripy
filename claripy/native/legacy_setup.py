from .clari_setup import Setup, clari
from . import legacy_module

import warnings # TODO: does angr roll its own? Do we hook this?
import weakref

class LegacySetup(Setup):
    def __init__(self, *, debug_mode: bool = False):
        msg = "Use setup_clari.Setup instead of LegacySetup"
        warnings.warn(msg, DeprecationWarning)
        super().__init__(debug_mode=debug_mode)

    def define_members(self):
        super().define_members()
        clari.Legacy = legacy_module
        self._enable_args()

    @staticmethod
    def _enable_args():
        def _args(self):
            if self not in self._args_dict:  # Cache check
                lst = self.op.python_children()
                print(type(self.op))
                if self.op.is_leaf:
                    lst.append(len(self))
                self._args_dict[self] = tuple(lst)
            return self._args_dict[self]

        # Claricpp objects are generally readonly, so we map weakrefs to cached vars
        clari.Expr.Base._args_dict = weakref.WeakKeyDictionary()
        clari.Expr.Base.args = property(_args)

__all__ = ('LegacySetup', 'clari',)