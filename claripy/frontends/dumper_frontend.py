import logging
import sys
import threading
from ..utils.transition import raise_from

from .constrained_frontend import ConstrainedFrontend

l = logging.getLogger("claripy.frontends.dumper_frontend")

class DumperFrontend(ConstrainedFrontend):

    def __init__(self, solver_backend, timeout=None, track=False, **kwargs):
        ConstrainedFrontend.__init__(self, **kwargs)
        self._track = track
        self._solver_backend = solver_backend

    def satisfiable(self, extra_constraints=(), exact=None):
        # TODO: Where are all the current constraints
        try:
            return self._solver_backend.satisfiable(
                extra_constraints=self.constraints,
            )
        except BackendError as e:
            raise_from(ClaripyFrontendError("Backend error during solve"), e)

    # def eval(self, e, n, extra_constraints=(), exact=None):
    #     if not self.satisfiable(extra_constraints=extra_constraints):
    #         raise UnsatError('unsat')

    def get_smtlib_script_satisfiability(self, extra_constraints=()):
        """
        Return an smt-lib script that check the satisfiability of the current constraints

        :return string: smt-lib script
        """
        try:
            import ipdb; ipdb.set_trace()
            return self._solver_backend._get_satisfiability_smt_script(
                extra_constraints=self._solver_backend.convert_list(tuple(self.constraints) + extra_constraints))
        except BackendError as e:
            raise_from(ClaripyFrontendError("Backend error during solve"), e)

    # def merge(self, others, merge_conditions, common_ancestor=None):
    #     return self._solver_backend.__class__.__name__ == 'BackendZ3', ConstrainedFrontend.merge(
    #         self, others, merge_conditions, common_ancestor=common_ancestor
    #     )[1]

from ..errors import UnsatError, BackendError, ClaripyFrontendError
from ..ast.bv import UGE, ULE
from ..backend_manager import backends
