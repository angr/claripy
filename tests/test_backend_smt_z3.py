import unittest

import common_backend_smt_solver

import claripy
from claripy.backends.backend_smtlib_solvers.z3_popen import SolverBackendZ3


class SmtLibSolverTest_Z3(common_backend_smt_solver.SmtLibSolverTestBase):
    @unittest.skip("Skip these test for now because of a problem with pysmt")
    def get_solver(self):
        backend = SolverBackendZ3(daggify=True)
        solver = claripy.SolverStrings(backend=backend)
        return solver


if __name__ == "__main__":
    suite = unittest.TestLoader().loadTestsFromTestCase(SmtLibSolverTest_Z3)
    unittest.TextTestRunner(verbosity=2).run(suite)
