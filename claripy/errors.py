class ClaripyError(Exception):
    pass

class ClaripySatFailError(ClaripyError):
    pass

class ClaripySatTimeoutError(ClaripySatFailError):
    pass

class ClaripyUnsatError(ClaripySatFailError):
    pass

class ClaripyFrontendError(ClaripyError):
    pass

class ClaripySerializationError(ClaripyError):
    pass

class BackendError(ClaripyError):
    pass

class ClaripyZ3Error(ClaripyError):
    pass

class ClaripyBackendVSAError(BackendError):
    pass

class ClaripyVSASimplifierError(ClaripyBackendVSAError):
    pass

#
# AST errors
#

class ClaripyASTError(ClaripyError):
    pass

class ClaripyTypeError(ClaripyASTError):
    pass

class ClaripySizeError(ClaripyASTError):
    pass

class ClaripyOperationError(ClaripyASTError):
    pass

class ClaripyRecursionError(ClaripyOperationError):
    pass
