#!/usr/bin/env python

# pylint: disable=F0401,W0401,W0603,

import logging
l = logging.getLogger("claripy")

Claripies = { }

from .expression import E
from .ast import A
from . import bv
from .result import Result
from .errors import *
from .claripy_standalone import ClaripyStandalone
from .bv import BVV
from . import operations
from . import backends

def init_claripies():
    backend_vsa = backends.BackendVSA()
    backend_concrete = backends.BackendConcrete()
    Claripies['VSA'] = ClaripyStandalone('VSA', model_backends=[backend_concrete, backend_vsa], solver_backends=[])

    Claripies['ParallelZ3'] = ClaripyStandalone('ParallelZ3', parallel=True)
    Claripies['SerialZ3'] = ClaripyStandalone('SerialZ3', parallel=False)

init_claripies()

#from .operations import *
#from .wrapper import Wrapper, wrap, unwrap
#from .solver import Solver, sat, unsat
#from .utils import *
#from .composite_solver import CompositeSolver
#from .bv import BV, BVV
#
#empty_solver = Solver()
#empty_solver.check()
