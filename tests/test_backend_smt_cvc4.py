import unittest
import claripy
from claripy.backends import SolverBackendCVC4
from test_backend_smt_solver import SmtLibSolverTest


class SmtLibSolverTest_CVC4(SmtLibSolverTest):
    def get_solver(self):
        backend = SolverBackendCVC4(daggify=True)
        solver = claripy.SolverStrings(backend=backend)
        return solver


if __name__ == "__main__":
    suite = unittest.TestLoader().loadTestsFromTestCase(SmtLibSolverTest_CVC4)
    unittest.TextTestRunner(verbosity=2).run(suite)
