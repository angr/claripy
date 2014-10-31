#!/usr/bin/env python

# pylint: disable=F0401,W0401,W0603,

import logging
l = logging.getLogger("claripy")

Claripies = { }

from .ast import A, I
from . import bv
from .result import Result
from .errors import *
from .claripy_standalone import ClaripyStandalone
from .bv import BVV
from . import operations
from . import backends
from .vsa import *

def init_claripies():
    backend_vsa = backends.BackendVSA()
    backend_concrete = backends.BackendConcrete()
    Claripies['VSA'] = ClaripyStandalone('VSA', model_backends=[backend_concrete, backend_vsa], solver_backends=[])
    backend_vsa.set_claripy_object(Claripies['VSA'])
    backend_concrete.set_claripy_object(Claripies['VSA'])

    Claripies['ParallelZ3'] = ClaripyStandalone('ParallelZ3', parallel=True)
    Claripies['SerialZ3'] = ClaripyStandalone('SerialZ3', parallel=False)

    backend_concrete = backends.BackendConcrete()
    Claripies['Concrete'] = ClaripyStandalone('Concrete', model_backends=[backend_concrete], solver_backends=[], parallel=False)
    backend_concrete.set_claripy_object(Claripies['Concrete'])

init_claripies()

import sys
recurse = 25000
l.warning("Claripy is setting the recursion limit to %d. If Python segfaults, I am sorry.", recurse)
sys.setrecursionlimit(recurse)

#from .operations import *
#from .wrapper import Wrapper, wrap, unwrap
#from .solver import Solver, sat, unsat
#from .utils import *
#from .composite_solver import CompositeSolver
#from .bv import BV, BVV
#
#empty_solver = Solver()
#empty_solver.check()
