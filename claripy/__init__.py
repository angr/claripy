#!/usr/bin/env python
# pylint: disable=F0401,W0401,W0603,

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
# (unfortunately, this is the least hacky hack)
from . import backend_manager as _backend_manager
from . import backends as _backends_module
from .backends import Backend

#
# connect to ANA
#

import ana
if os.environ.get('REMOTE', False):
    ana.set_dl(ana.MongoDataLayer(()))

#
# Some other misguided setup
#

_recurse = 15000
l.warning("Claripy is setting the recursion limit to %d. If Python segfaults, I am sorry.", _recurse)
sys.setrecursionlimit(_recurse)

#
# backend objects
#

from . import bv
from . import fp
from . import vsa
from .fp import FSORT_DOUBLE, FSORT_FLOAT
from .annotations import *

#
# Operations
#

from .simplifier import simplifier

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

#
# Initialize the backends
#

from . import backend_manager as _backend_manager
_backend_manager.backends._register_backend(_backends_module.BackendConcrete(), 'concrete', True, True)
_backend_manager.backends._register_backend(_backends_module.BackendVSA(), 'vsa', False, False)
_backend_manager.backends._register_backend(_backends_module.BackendLength(), 'length', False, False)
_backend_manager.backends._register_backend(_backends_module.BackendSymbolic(), 'symbolic', False, False)
_backend_manager.backends._register_backend(_backends_module.BackendVariables(), 'variables', False, False)
_backend_manager.backends._register_backend(_backends_module.BackendDepth(), 'depth', False, False)
_backend_manager.backends._register_backend(_backends_module.BackendASTType(), 'ast_type', False, False)
_backend_manager.backends._register_backend(_backends_module.BackendITEExcavator(), 'ite_excavator', False, False)
_backend_manager.backends._register_backend(_backends_module.BackendITEBurrower(), 'ite_burrower', False, False)
_backend_z3 = _backends_module.BackendZ3()
_backend_manager.backends._register_backend(_backend_z3, 'z3', False, False)
backends = _backend_manager.backends

def downsize():
    backends.downsize()

#
# some standard ASTs
#

#true = BoolV(True)
#false = BoolV(False)
ast.true = true
ast.false = false
_all_operations.true = true
_all_operations.false = false

#
# Frontends
#

from .frontend import Frontend as _Frontend
from . import frontends
from . import frontend_mixins
from .solvers import *
