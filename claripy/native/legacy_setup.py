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
    def _fix_arg(arg):
        if type(arg) is clari.BigInt:
            return int(arg.value)
        return arg

    @classmethod
    def _enable_args(cls):
        def _args(self):
            if self not in self._args_dict:  # Cache check
                lst = [ cls._fix_arg(i) for i in self.op.python_children() ]
                # Add extra size arg if needed
                if type(self.op) is clari.Op.Literal:
                    if type(self) is clari.Expr.FP:
                        lst.append(FSORT_DOUBLE if len(self) == 64 else FSORT_FLOAT)
                    elif type(self) is not clari.Expr.Bool:
                        lst.append(len(self))
                elif type(self.op) is clari.Op.Symbol:
                    if type(self) is clari.Expr.String:
                        lst.append(self._uninitialized)
                    elif type(self) is clari.Expr.FP:
                        lst.append(FSORT_DOUBLE if len(self) == 64 else FSORT_FLOAT)
                # Save result
                self._args_dict[self] = tuple(lst)
            return self._args_dict[self]

        # Claricpp objects are generally readonly, so we map weakrefs to cached vars
        clari.Expr.Base._args_dict = weakref.WeakKeyDictionary()
        clari.Expr.Base.args = property(_args)

__all__ = ('LegacySetup', 'clari',)

from ..fp import FSORT_DOUBLE, FSORT_FLOAT
