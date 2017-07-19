"""
Collection of claripy VSA errors.
"""

from ..errors import ClaripyError

class ClaripyVSAError(ClaripyError):
    pass

class ClaripyVSAOperationError(ClaripyVSAError):
    pass
