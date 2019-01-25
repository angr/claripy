import unittest
import claripy
import nose
from claripy.backends.backend_smtlib_solvers.z3_popen import SolverBackendZ3
from test_backend_smt_solver import SmtLibSolverTest


class SmtLibSolverTest_Z3(SmtLibSolverTest):
    def get_solver(self):
        # Skip these test for now because of a problem with pysmt
        raise nose.SkipTest()
        if 'smtlib_z3' not in claripy.backends._backends_by_name:
            raise nose.SkipTest()

        backend = SolverBackendZ3(daggify=True)
        solver = claripy.SolverStrings(backend=backend)
        return solver


if __name__ == "__main__":
    suite = unittest.TestLoader().loadTestsFromTestCase(SmtLibSolverTest_Z3)
    unittest.TextTestRunner(verbosity=2).run(suite)

