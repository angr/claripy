__all__ = [ 'Z3' ]

from claricpp import *
from backend import Backend
from enum import Enum
from functools import cache, cached_property

# TODO: deal with destruction / freeing memory
# TODO: slots!


class Z3(Backend):
    '''
    The public API for the Z3 backend
    '''
    def __init__(self):
        self._backend = claricpp.claricpp_backend_z3_new()

    def solver(self, timeout = 0, *, force_new = False):
        if force_new:
            return claricpp.claricpp_backend_z3_new_tls_solver(self._backend, timeout)
        else:
            return claricpp.claricpp_backend_z3_tls_solver(self._backend, timeout)
