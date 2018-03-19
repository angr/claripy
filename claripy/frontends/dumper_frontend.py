import logging
import sys
import threading
from ..utils.transition import raise_from

from .constrained_frontend import ConstrainedFrontend

l = logging.getLogger("claripy.frontends.full_frontend")

class DumperFrontend(ConstrainedFrontend):
    _model_hook = None

    def __init__(self, solver_backend, timeout=None, track=False, **kwargs):
        ConstrainedFrontend.__init__(self, **kwargs)
        self._solver_backend = solver_backend
        self._solver_backend.register_solver(self)
        self._assertion_stack = []


    def get_assertions(self):
        return self._assertion_stack

    def push(self, assertion):
        self._assertion_stack.append(assertion)


    def pop(self):
        self._assertion_stack.pop()


    def satisfiable(self, extra_constraints=(), exact=None):
        # TODO: Deal with extra constrains
        try:
            return self._solver_backend.satisfiable(
                extra_constraints=extra_constraints,
            )
        except BackendError as e:
            raise_from(ClaripyFrontendError("Backend error during solve"), e)


    def get_smtlib_script_satisfiability(self,  extra_constraints=()):
        try:
            return self._solver_backend._get_satisfiability_smt_script(
                extra_constraints=self._solver_backend.convert_list(self.constraints))
        except BackendError as e:
            raise_from(ClaripyFrontendError("Backend error during solve"), e)


from ..errors import UnsatError, BackendError, ClaripyFrontendError
