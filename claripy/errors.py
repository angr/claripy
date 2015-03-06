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

class ClaripySolverError(ClaripyError):
    pass

class ClaripyExpressionError(ClaripyError):
    pass

class ClaripySerializationError(ClaripyError):
    pass

class BackendError(ClaripyError):
    pass

class ClaripyZ3Error(ClaripyError):
    pass

class ClaripyBackendVSAError(BackendError):
    pass

class ClaripyRecursionError(ClaripyOperationError):
    pass