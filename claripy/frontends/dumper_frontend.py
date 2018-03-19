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
        self._solver_backend.register_solver(self)
        # The assertion stack keeps track of all the declared variables
        self._assertion_stack = []

    # def _blank_copy(self, c):
    #     super(FullFrontend, self)._blank_copy(c)
    #     c._track = self._track
    #     c._solver_backend = self._solver_backend
    #     c.timeout = self.timeout
    #     c._tls = threading.local()
    #     c._to_add = [ ]

    def get_assertions(self):
        """
        Return current assertion stack
        """
        return self._assertion_stack

    def push(self, assertion):
        """
        Push a new assertion on the assertion stack

        :param assertion: Assertion that needs to be pushed
        """
        self._assertion_stack.append(assertion)

    # def _ana_getstate(self):
    #     return self._solver_backend.__class__.__name__, self.timeout, self._track, ConstrainedFrontend._ana_getstate(self)

    def pop(self):
        """
        Pop an assertion from the assertion stack
        """
        self._assertion_stack.pop()

    # #
    # # Frontend Creation
    # #

    # def _get_solver(self):
    #     if getattr(self._tls, 'solver', None) is None or (self._finalized and len(self._to_add) > 0):
    #         self._tls.solver = self._solver_backend.solver(timeout=self.timeout)
    #         self._add_constraints()

    #     if len(self._to_add) > 0:
    #         self._add_constraints()

    #     return self._tls.solver

    # def _add_constraints(self):
    #     self._solver_backend.add(self._tls.solver, self.constraints, track=self._track)
    #     self._to_add = [ ]

    # #
    # # Constraint management
    # #

    def add(self, constraints):
        try:
            to_add = ConstrainedFrontend.add(self, constraints)
            # TODO: Understand if this is a correct way to do this
            #       (software engineering POV)
            self._to_add += to_add
            self._solver_backend._add(self._solver_backend.convert(self.constraints[-1]))
            return to_add
        except BackendError as e:
            raise_from(ClaripyFrontendError("Backend error during add"), e)

    # def simplify(self):
    #     ConstrainedFrontend.simplify(self)

    #     # TODO: should we do this?
    #     self._tls.solver = None
    #     self._to_add = [ ]

    #     return self.constraints

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

    def get_smtlib_script_satisfiability(self,  extra_constraints=()):
        """
        Return an smt-lib script that check the satisfiability of the current constraints

        :return string: smt-lib script
        """
        try:
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
