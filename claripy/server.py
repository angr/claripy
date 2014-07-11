from .claripy import Claripy
from .backends import BackendZ3, BackendConcrete

import logging
l = logging.getLogger("claripy.server")

class ClaripyServer(Claripy):
    def __init__(self):
        backends = [ BackendConcrete(), BackendZ3() ]
        Claripy.__init__(self, backends)

    def solver(self):
        return ServerSolver(claripy=self)
