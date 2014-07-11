from .claripy import Claripy
from .backends import BackendAbstract, BackendConcrete
from .solvers import ClientSolver

import logging
l = logging.getLogger("claripy.client")

class ClaripyClient(Claripy):
    def __init__(self):
        backends = [ BackendConcrete(), BackendAbstract() ]
        Claripy.__init__(self, backends)

    def solver(self):
        return ClientSolver(claripy=self)
