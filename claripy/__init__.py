#!/usr/bin/env python

# pylint: disable=F0401,W0401,W0603,

import logging
l = logging.getLogger("claripy")

claripy = None
def set_claripy(c):
    global claripy
    claripy = c
    return c

def get_claripy():
    return claripy

from .expression import E, A
from . import bv
from . import datalayer
from .result import Result
from .errors import *
from .claripy_standalone import ClaripyStandalone
from .datalayer import DataLayer
from .bv import BVV
from . import operations
from . import backends

def init_standalone(model_backend=None, solver_backends=None):
    return set_claripy(ClaripyStandalone(model_backend=model_backend, solver_backends=solver_backends))

#from .operations import *
#from .wrapper import Wrapper, wrap, unwrap
#from .solver import Solver, sat, unsat
#from .utils import *
#from .composite_solver import CompositeSolver
#from .bv import BV, BVV
#
#empty_solver = Solver()
#empty_solver.check()
