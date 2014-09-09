class ClaripyError(Exception):
    pass

class UnsatError(ClaripyError):
    pass

class ClaripyTypeError(ClaripyError):
    pass

class ClaripySizeError(ClaripyError):
    pass

class ClaripyOperationError(ClaripyError):
    pass

class BackendError(ClaripyError):
    pass
