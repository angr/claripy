import logging
import sys
import threading
from ..utils.transition import raise_from

from .constrained_frontend import ConstrainedFrontend

l = logging.getLogger("claripy.frontends.dumper_frontend")

class DumperFrontend(ConstrainedFrontend):

    def __init__(self, solver_backend, timeout=None, track=False, **kwargs):
        ConstrainedFrontend.__init__(self, **kwargs)
        self._solver_backend = solver_backend

    def get_smtlib_script_satisfiability(self, extra_constraints=()):
        """
        Return an smt-lib script that check the satisfiability of the current constraints

        :return string: smt-lib script
        """
        try:
            return self._solver_backend._get_satisfiability_smt_script(
                constraints=self._solver_backend.convert_list(tuple(self.constraints) + extra_constraints))
        except BackendError as e:
            raise_from(ClaripyFrontendError("Backend error during solve"), e)


from ..errors import UnsatError, BackendError, ClaripyFrontendError
