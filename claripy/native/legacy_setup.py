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
        # Fix wonky
        old_ls = clari.Create.literal_string
        clari.Create.literal_string = lambda s, l: old_ls(s.ljust(l, "\0"))
        old_u = clari.Create.union_
        clari.Create.union_ = lambda *args: old_u(*(args[0] if len(args) == 1 else args))
        # TODO: ^ check with fish
        super().define_members()
        clari.Legacy = legacy_module
        self._enable_args()
        # Init the module
        clari.Legacy.init()
        del clari.Legacy.init

    @staticmethod
    def _enable_args():
        fix = lambda x: int(x.value) if isinstance(x, clari.BigInt) else x
        def _args(self):
            if self not in self._args_dict:  # Cache check
                args = tuple([fix(i) for i in self.op.python_children()])
                self._args_dict[self] = args
            return self._args_dict[self]

        # Claricpp objects are generally readonly, so we map weakrefs to cached vars
        clari.Expr.Base._args_dict = weakref.WeakKeyDictionary()
        clari.Expr.Base.args = property(_args)

__all__ = ('LegacySetup', 'clari',)
