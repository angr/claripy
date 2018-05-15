import unittest
import claripy
from claripy.backends.backend_smtlib_solvers.cvc4_popen import SolverBackendCVC4
from test_backend_smt_solver import SmtLibSolverTest


class SmtLibSolverTest_CVC4(SmtLibSolverTest):
    def get_solver(self):
        backend = SolverBackendCVC4(daggify=True, smt_script_log_dir=None)
        solver = claripy.SolverStrings(backend=backend, timeout=300000)
        return solver


if __name__ == "__main__":
    suite = unittest.TestLoader().loadTestsFromTestCase(SmtLibSolverTest_CVC4)
    unittest.TextTestRunner(verbosity=2).run(suite)
