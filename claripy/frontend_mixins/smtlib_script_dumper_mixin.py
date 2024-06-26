import logging

from claripy.errors import BackendError, ClaripyFrontendError

l = logging.getLogger(__name__)


class SMTLibScriptDumperMixin:
    def get_smtlib_script_satisfiability(self, extra_constraints=(), extra_variables=()):
        """
        Return an smt-lib script that check the satisfiability of the current constraints

        :return string: smt-lib script
        """
        try:
            e_csts = self._solver_backend.convert_list(extra_constraints + tuple(self.constraints))
            e_variables = self._solver_backend.convert_list(extra_variables)

            variables, csts = self._solver_backend._get_all_vars_and_constraints(e_c=e_csts, e_v=e_variables)
            return self._solver_backend._get_satisfiability_smt_script(csts, variables)
        except BackendError as e:
            raise ClaripyFrontendError("Backend error during smtlib script generation") from e
