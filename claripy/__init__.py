#!/usr/bin/env python

# pylint: disable=F0401,W0401,W0603,

import logging
l = logging.getLogger("claripy")

from .expression import E, A
from . import bv
from . import datalayer
from .result import Result, UnsatError
from .claripy_standalone import ClaripyStandalone
from .datalayer import DataLayer
from .bv import BVV
from . import backends

claripy = None
def set_claripy(c):
    global claripy
    claripy = c

def init_standalone():
    set_claripy(ClaripyStandalone())

#from .operations import *
#from .wrapper import Wrapper, wrap, unwrap
#from .solver import Solver, sat, unsat
#from .utils import *
#from .composite_solver import CompositeSolver
#from .bv import BV, BVV
#
#empty_solver = Solver()
#empty_solver.check()
