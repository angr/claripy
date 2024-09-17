# pylint: disable=F0401,W0401,W0603,

__version__ = "9.2.118"

if bytes is str:
    raise Exception("This module is designed for python 3 only. Please install an older version to use python 2.")

from .errors import *
from . import operations as operations

# This is here for later, because we'll fuck the namespace in a few lines
from . import backends as _backends_module
from .backends.backend import Backend as Backend
from .backend_object import BackendObject as BackendObject


#
# backend objects
#

from . import bv as bv
from . import fp as fp
from . import vsa as vsa
from .fp import FSORT_DOUBLE as FSORT_DOUBLE, FSORT_FLOAT as FSORT_FLOAT
from .annotation import *

#
# Operations
#

from .ast.base import *
from .ast.bv import *
from .ast.fp import *
from .ast.bool import *
from .ast.strings import *
from . import ast

del BV
del Bool
del FP
del Base
ast._import()


def BV(name, size, explicit_name=None):  # pylint:disable=function-redefined
    l.critical(
        "DEPRECATION WARNING: claripy.BV is deprecated and will soon be removed. Please use claripy.BVS, instead."
    )
    print("DEPRECATION WARNING: claripy.BV is deprecated and will soon be removed. Please use claripy.BVS, instead.")
    return BVS(name, size, explicit_name=explicit_name)


#
# Initialize the backends
#

from . import backend_manager as _backend_manager

# The order these backends are registered in is the order they will be tried in
# certain operations, importantly simplification. VSA is last because if an
# expression can be simplified with concrete or z3, we want to use that first
_backend_manager.backends._register_backend(_backends_module.BackendConcrete(), "concrete")
_backend_manager.backends._register_backend(_backends_module.BackendZ3(), "z3")
_backend_manager.backends._register_backend(_backends_module.BackendVSA(), "vsa")
backends = _backend_manager.backends


def downsize():
    """
    Clear all temporary data associated with any backend
    """
    backends.downsize()


#
# Frontends
#

from .frontend import Frontend as _Frontend
from . import frontends as frontends
from . import frontend_mixins as frontend_mixins
from .solvers import *

#
# Convenient button
#


def reset():
    """
    Attempt to refresh any caching state associated with the module
    """
    downsize()
    from .ast import bv  # pylint:disable=redefined-outer-name

    bv._bvv_cache.clear()


from .debug import set_debug
