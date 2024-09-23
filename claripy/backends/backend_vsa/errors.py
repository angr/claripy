from __future__ import annotations

from claripy.errors import ClaripyError


class ClaripyVSAError(ClaripyError):
    pass


class ClaripyVSAOperationError(ClaripyVSAError):
    pass
