#!/usr/bin/env python

# pylint: disable=F0401,W0401,W0603,

import sys
import logging
l = logging.getLogger("claripy")

_all_backends = [ ]
_eager_backends = [ ]
_model_backends = [ ]

from .errors import *
from . import operations
from . import ops as _all_operations

from . import backends as _backends
_backend_vsa = _backends.BackendVSA()
_backend_z3 = _backends.BackendZ3()
_backend_concrete = _backends.BackendConcrete()

_eager_backends[:] = [ _backend_concrete ]
_model_backends[:] = [ _backend_concrete, _backend_vsa ]
_all_backends[:] = [ _backend_concrete, _backend_vsa, _backend_z3 ]

_recurse = 15000
l.warning("Claripy is setting the recursion limit to %d. If Python segfaults, I am sorry.", _recurse)
sys.setrecursionlimit(_recurse)

#
# Below are some exposed interfaces for general use.
#

def downsize():
    _backend_vsa.downsize()
    _backend_concrete.downsize()
    _backend_z3.downsize()

#
# solvers
#

from .solvers import BranchingSolver, CompositeSolver
Solver = BranchingSolver
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

from .ast_base import *
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
