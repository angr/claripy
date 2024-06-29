# pylint: disable=missing-class-docstring,no-self-use
import unittest

import common_backend_smt_solver

import claripy


class TestSmtLibSolverTest_Z3(common_backend_smt_solver.SmtLibSolverTestBase):
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
    unittest.main()
