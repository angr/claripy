import unittest
import claripy
import common_backend_smt_solver


class SmtLibSolverTest_ABC(common_backend_smt_solver.SmtLibSolverTestBase):
    @common_backend_smt_solver.if_installed
    def get_solver(self):
        from claripy.backends.backend_smtlib_solvers.abc_popen import SolverBackendABC

        backend = SolverBackendABC(daggify=True)
        solver = claripy.SolverStrings(backend=backend)
        return solver


if __name__ == "__main__":
    suite = unittest.TestLoader().loadTestsFromTestCase(SmtLibSolverTest_ABC)
    unittest.TextTestRunner(verbosity=2).run(suite)
