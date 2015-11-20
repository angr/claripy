#!/usr/bin/env python

# pylint: disable=F0401,W0401,W0603,

import os
import sys
import socket
import logging
l = logging.getLogger("claripy")
l.addHandler(logging.NullHandler())

_all_backends = [ ]
_trusted_backends = [ ]
_eager_backends = [ ]
_model_backends = [ ]
_backends = { }

from .errors import *
from . import operations
from . import ops as _all_operations

from . import backends as _backends_module
backend_vsa = _backends_module.BackendVSA()
backend_concrete = _backends_module.BackendConcrete()

if not os.environ.get('WORKER', False) and os.environ.get('REMOTE', False):
    try:
        backend_z3 = _backends_module.backendremote.BackendRemote()
    except socket.error:
        raise ImportError("can't connect to backend")
else:
    backend_z3 = _backends_module.BackendZ3()

_eager_backends[:] = [ backend_concrete ]
_model_backends[:] = [ backend_concrete, backend_vsa ]
_trusted_backends[:] = [ backend_concrete, backend_z3 ]
_all_backends[:] = [ backend_concrete, backend_vsa, backend_z3 ]
_backends.update({ 'BackendVSA': backend_vsa, 'BackendZ3': backend_z3, 'BackendConcrete': backend_concrete })

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
from .frontends import LightFrontend, FullFrontend, CompositeFrontend, HybridFrontend, ReplacementFrontend
def Solver():
    return HybridFrontend(backend_z3)
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
del BV
del Bool
del FP
del Base
ast._import()

def BV(name, size, explicit_name=None): #pylint:disable=function-redefined
    l.critical("DEPRECATION WARNING: claripy.BV is deprecated and will soon be removed. Please use claripy.BVS, instead.")
    print "DEPRECATION WARNING: claripy.BV is deprecated and will soon be removed. Please use claripy.BVS, instead."
    return BVS(name, size, explicit_name=explicit_name)
