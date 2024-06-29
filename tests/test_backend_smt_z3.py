# pylint: disable=missing-class-docstring,no-self-use
import unittest

import common_backend_smt_solver

import claripy
from claripy.backends.backend_smtlib_solvers.z3_popen import SolverBackendZ3


class TestSmtLibSolverTest_Z3(common_backend_smt_solver.SmtLibSolverTestBase):
    @unittest.skip("Skip these test for now because of a problem with pysmt")
    def get_solver(self):
        backend = SolverBackendZ3(daggify=True)
        solver = claripy.SolverStrings(backend=backend)
        return solver


if __name__ == "__main__":
    unittest.main()
