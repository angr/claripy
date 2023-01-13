import unittest
import claripy
from claripy.backends.backend_smtlib_solvers.z3_popen import SolverBackendZ3
import common_backend_smt_solver


class SmtLibSolverTest_Z3(common_backend_smt_solver.SmtLibSolverTestBase):
    @unittest.skip("Skip these test for now because of a problem with pysmt")
    def get_solver(self):
        solver = claripy.SolverPortfolio(
            solvers=[
                claripy.SolverComposite(
                    template_solver_string=claripy.SolverCompositeChild(
                        backend=claripy.backend_manager.backends.smtlib_cvc4
                    )
                ),
                claripy.SolverComposite(
                    template_solver_string=claripy.SolverCompositeChild(
                        backend=claripy.backend_manager.backends.smtlib_z3
                    )
                ),
                claripy.SolverComposite(
                    template_solver_string=claripy.SolverCompositeChild(
                        backend=claripy.backend_manager.backends.smtlib_z3str
                    )
                ),
            ]
        )
        return solver


if __name__ == "__main__":
    suite = unittest.TestLoader().loadTestsFromTestCase(SmtLibSolverTest_Z3)
    unittest.TextTestRunner(verbosity=2).run(suite)
