#!/usr/bin/env python

# pylint: disable=F0401,W0401,W0603,

import socket
import os

import logging
l = logging.getLogger("claripy")

Claripies = { }

from .ast import Base, Bits, BV, FP
from . import bv
from .result import Result
from .errors import *
from .claripy_standalone import ClaripyStandalone
from .bv import BVV
from .fp import FPV, FSORT_FLOAT, FSORT_DOUBLE, FSort, RM, RM_RTN, RM_RTP, RM_RNE, RM_RTZ
from . import operations
from . import backends
from .vsa import *
from .backend import Backend, BackendObject
from .backends import backendremote

g_conn = None

def init_claripies():
    global g_conn

    backend_vsa = backends.BackendVSA()
    backend_concrete = backends.BackendConcrete()
    Claripies['VSA'] = ClaripyStandalone('VSA', model_backends=[backend_concrete, backend_vsa], solver_backends=[])
    backend_vsa.set_claripy_object(Claripies['VSA'])
    backend_concrete.set_claripy_object(Claripies['VSA'])

    Claripies['ParallelZ3'] = ClaripyStandalone('ParallelZ3', parallel=True)
    Claripies['RealSerialZ3'] = ClaripyStandalone('RealSerialZ3', parallel=False)

    if os.environ.get('WORKER', False):
        Claripies['SerialZ3'] = ClaripyStandalone('SerialZ3', parallel=False)
    else:
        if os.environ.get('REMOTE', False):
            try:
                br = backendremote.BackendRemote()
                Claripies['SerialZ3'] = ClaripyStandalone('SerialZ3', solver_backends=[br], parallel=False)
                br.set_claripy_object(Claripies['SerialZ3'])
            except socket.error:
                pass
        else:
            Claripies['SerialZ3'] = ClaripyStandalone('SerialZ3', parallel=False)

    backend_concrete = backends.BackendConcrete()
    Claripies['Concrete'] = ClaripyStandalone('Concrete', model_backends=[backend_concrete], solver_backends=[], parallel=False)
    backend_concrete.set_claripy_object(Claripies['Concrete'])

init_claripies()

if os.environ.get('REMOTE', False):
    import ana
    ana.set_dl(mongo_args=())

import sys
recurse = 15000
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
