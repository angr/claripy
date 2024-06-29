# pylint: disable=missing-class-docstring,no-self-use
import unittest

import common_backend_smt_solver

import claripy


class TestSmtLibSolverTest_ABC(common_backend_smt_solver.SmtLibSolverTestBase):
    @common_backend_smt_solver.if_installed
    def get_solver(self):
        from claripy.backends.backend_smtlib_solvers.abc_popen import SolverBackendABC

        backend = SolverBackendABC(daggify=True)
        solver = claripy.SolverStrings(backend=backend)
        return solver


if __name__ == "__main__":
    unittest.main()
