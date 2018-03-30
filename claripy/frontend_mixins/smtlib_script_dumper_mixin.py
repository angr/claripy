import logging
import sys
import threading
from ..utils.transition import raise_from

from ..frontends.constrained_frontend import ConstrainedFrontend

l = logging.getLogger(__name__)

class SMTLibScriptDumperMixin(object):
    def get_smtlib_script_satisfiability(self, extra_constraints=()):
        """
        Return an smt-lib script that check the satisfiability of the current constraints

        :return string: smt-lib script
        """
        try:
            return self._solver_backend._get_satisfiability_smt_script(
                constraints=self._solver_backend.convert_list(tuple(self.constraints) + extra_constraints))
        except BackendError as e:
            raise_from(ClaripyFrontendError("Backend error during smtlib script generation"), e)

    # def merge(self, others, merge_conditions, common_ancestor=None):
    #     return self._solver_backend.__class__.__name__ == 'BackendZ3', ConstrainedFrontend.merge(
    #         self, others, merge_conditions, common_ancestor=common_ancestor
    #     )[1]

from ..errors import BackendError, ClaripyFrontendError
