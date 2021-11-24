import unittest
from unittest import skip
import claripy
from claripy.backends.backend_smtlib_solvers.z3_popen import SolverBackendZ3
import common_backend_smt_solver
from common_backend_smt_solver import if_installed


class SmtLibSolverTest_Z3(common_backend_smt_solver.SmtLibSolverTestBase):
    # Skip these test for now because of a problem with pysmt
    @if_installed
    def get_solver(self):
        backend = SolverBackendZ3(daggify=True)
        solver = claripy.SolverStrings(backend=backend)
        return solver


if __name__ == "__main__":
    suite = unittest.TestLoader().loadTestsFromTestCase(SmtLibSolverTest_Z3)
    unittest.TextTestRunner(verbosity=2).run(suite)

