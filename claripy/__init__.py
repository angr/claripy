#!/usr/bin/env python

# pylint: disable=F0401,W0401,W0603,

import os
import sys
import socket
import logging
l = logging.getLogger("claripy")
l.addHandler(logging.NullHandler())

_all_backends = [ ]
_eager_backends = [ ]
_model_backends = [ ]

from .errors import *
from . import operations
from . import ops as _all_operations

from . import backends as _backends
backend_vsa = _backends.BackendVSA()

if not os.environ.get('WORKER', False) and os.environ.get('REMOTE', False):
    try:
        backend_z3 = _backends.backendremote.BackendRemote()
    except socket.error:
        raise ImportError("can't connect to backend")
else:
    backend_z3 = _backends.BackendZ3()

backend_concrete = _backends.BackendConcrete()

_eager_backends[:] = [ backend_concrete ]
_model_backends[:] = [ backend_concrete, backend_vsa ]
_all_backends[:] = [ backend_concrete, backend_vsa, backend_z3 ]
_backends = { 'BackendVSA': backend_vsa, 'BackendZ3': backend_z3, 'BackendConcrete': backend_concrete }

#
# connect to ANA
#

import ana
if os.environ.get('REMOTE', False):
    ana.set_dl(mongo_args=())

#
# Some other misguided setup
#

_recurse = 15000
l.warning("Claripy is setting the recursion limit to %d. If Python segfaults, I am sorry.", _recurse)
sys.setrecursionlimit(_recurse)

#
# Below are some exposed interfaces for general use.
#

def downsize():
    backend_vsa.downsize()
    backend_concrete.downsize()
    backend_z3.downsize()

#
# solvers
#

from .frontend import Frontend as _Frontend
from .frontends import LightFrontend, FullFrontend, CompositeFrontend
def Solver():
    return FullFrontend(backend_z3)
from .result import Result

#
# backend objects
#

from . import bv
from . import fp
from . import vsa

#
# Operations
#

from .ast.base import *
from .ast.bv import *
from .ast.fp import *
from .ast.bool import *
from . import ast
ast._import()

#
# and some aliases
#

BVV = BitVecVal
BV = BitVec
VS = ValueSet
SI = StridedInterval
TSI = TopStridedInterval
ESI = EmptyStridedInterval
