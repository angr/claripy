#!/usr/bin/env python
# pylint: disable=F0401,W0401,W0603,

__version__ = (8, 20, 6, 1)

if bytes is str:
    raise Exception("This module is designed for python 3 only. Please install an older version to use python 2.")

import os
import sys
import socket
import logging
l = logging.getLogger("claripy")
l.addHandler(logging.NullHandler())

from .errors import *
from . import operations
from . import ops as _all_operations

# This is here for later, because we'll fuck the namespace in a few lines
from . import backends as _backends_module
from .backends import Backend
from .backend_object import BackendObject


#
# backend objects
#

from . import bv
from . import fp
from . import vsa
from .fp import FSORT_DOUBLE, FSORT_FLOAT
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

def BV(name, size, explicit_name=None): #pylint:disable=function-redefined
    l.critical("DEPRECATION WARNING: claripy.BV is deprecated and will soon be removed. Please use claripy.BVS, instead.")
    print("DEPRECATION WARNING: claripy.BV is deprecated and will soon be removed. Please use claripy.BVS, instead.")
    return BVS(name, size, explicit_name=explicit_name)

#
# Initialize the backends
#

from . import backend_manager as _backend_manager
_backend_manager.backends._register_backend(_backends_module.BackendConcrete(), 'concrete', True, True)
_backend_manager.backends._register_backend(_backends_module.BackendVSA(), 'vsa', False, False)

if not os.environ.get('WORKER', False) and os.environ.get('REMOTE', False):
    try:
        _backend_z3 = _backends_module.backendremote.BackendRemote()
    except socket.error:
        raise ImportError("can't connect to backend")
else:
    _backend_z3 = _backends_module.BackendZ3()

_backend_manager.backends._register_backend(_backend_z3, 'z3', False, False)
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
from . import frontends
from . import frontend_mixins
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
