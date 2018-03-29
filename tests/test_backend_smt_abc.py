import unittest
import claripy
from claripy.backends.backend_smtlib_solvers.abc_popen import SolverBackendABC
from test_backend_smt_solver import SmtLibSolverTest


class SmtLibSolverTest_ABC(SmtLibSolverTest):
    def get_solver(self):
        backend = SolverBackendABC(daggify=True)
        solver = claripy.SolverStrings(backend=backend)
        return solver


if __name__ == "__main__":
    suite = unittest.TestLoader().loadTestsFromTestCase(SmtLibSolverTest_ABC)
    unittest.TextTestRunner(verbosity=2).run(suite)

