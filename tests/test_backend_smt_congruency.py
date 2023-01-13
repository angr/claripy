import unittest
from abc import abstractmethod

import claripy
from collections import defaultdict

import time

NUMBER_SOLUTIONS_TO_COMPARE = 5


def solution_ast(var, val):
    if type(var) == claripy.ast.strings.String:
        return claripy.StringV(val)
    return (var == val).args[1]


def all_equal(vals):
    vals = tuple(vals)
    if not vals:
        return True
    v0 = vals[0]
    return all(v == v0 for v in vals)


class SmtLibSolverTestCongruency(unittest.TestCase):
    @unittest.skip("Skip these test for now because of a problem with pysmt")
    def get_solvers(self):
        solvers = [
            claripy.SolverStrings(backend=claripy.backend_manager.backends.smtlib_cvc4),
            claripy.SolverStrings(backend=claripy.backend_manager.backends.smtlib_z3),
            # claripy.SolverStrings(backend=claripy.backend_manager.backends.smtlib_z3str),
        ]
        return solvers

    def _get_models_it(self, solver, variables, constraints, n=None):
        if n is None:
            n = NUMBER_SOLUTIONS_TO_COMPARE

        vars = list(variables)
        results = solver.batch_eval(vars, n, extra_constraints=constraints)
        for r in results:
            yield map(lambda x: (x[0], solution_ast(*x)), zip(vars, r))

    def doublecheck_model_is_correct(self, csts, model):
        for c in csts:
            new = c
            for var, val in model:
                new = new.replace(var, val)
            self.assertTrue(new.is_true(), f"Either model is incomplete or wrong! Constraint: {c}, Model: {model}")

    def is_model_correct(self, csts, model):
        for c in csts:
            new = c
            for var, val in model:
                new = new.replace(var, val)
            if not c.is_true:
                return False
        return True

    def _collect_generic_solver_test_data(self, variables, constraints):
        solvers = self.get_solvers()
        vars = list(variables)

        results = defaultdict(dict)
        results["variables"] = variables
        results["constraints"] = constraints
        results["solvers"] = solvers
        for s in solvers:
            before_sat_check = time.time()
            results[s]["claimed_sat"] = s.satisfiable(extra_constraints=constraints)
            results[s]["solve_time"] = time.time() - before_sat_check
            results[s]["claimed_solutions"] = ()

            if results[s]["claimed_sat"]:
                before_eval = time.time()

                solutions = tuple(
                    self._get_models_it(s, variables, constraints=constraints, n=NUMBER_SOLUTIONS_TO_COMPARE)
                )

                results[s]["eval_time"] = time.time() - before_eval

                results[s]["claimed_solutions"] = solutions
                results[s]["num_requested_solutions"] = NUMBER_SOLUTIONS_TO_COMPARE
                results[s]["solution_correctness"] = tuple(self.is_model_correct(constraints, sol) for sol in solutions)

        return dict(results)

    def _generic_consistency_check(self, results):
        vs = results["variables"]
        cs = results["constraints"]

        for solver in results["solvers"]:
            solver_results = results[solver]
            if not solver_results["claimed_sat"]:
                continue
            for r in solver_results["claimed_solutions"]:
                self.doublecheck_model_is_correct(cs, r)

    def _generic_congruency_check(self, solvers, results):
        self.assertTrue(all_equal(results[s]["claimed_sat"] for s in solvers), "Solvers disagree on satisfiability")
        self.assertTrue(
            all_equal(len(results[s]["claimed_solutions"]) for s in solvers), "Solvers disagree on number of solutions!"
        )

    def test_congruency_1(self):
        recv_input = claripy.StringS("recv_input", 1024)
        constraints = []
        constraints.append(0 <= claripy.StrIndexOf(recv_input, claripy.StringV("\r\n\r\n"), 0, 32))

        results = self._collect_generic_solver_test_data((recv_input,), constraints)
        self._generic_consistency_check(results)
        self._generic_congruency_check(results["solvers"], results)

    def test_congruency_2(self):
        """
        (set-logic ALL)
        (declare-fun recv_input_4_1024 () String)
        (assert (< ( str.indexof recv_input_4_1024 "\r\n\r\n" 0) 0))
        (assert (<= 0 ( str.indexof recv_input_4_1024 " \r\n" 0)))
        (assert (<= 0 ( str.indexof recv_input_4_1024 " \r\n" (+ ( str.indexof recv_input_4_1024 " \r\n" 0) 1))))
        (assert (<= 0 ( str.indexof recv_input_4_1024 " \r\n" (+ ( str.indexof recv_input_4_1024 " \r\n" (+ ( str.indexof recv_input_4_1024 " \r\n" 0) 1)) 1))))
        (assert (= "GET"
        ( str.substr
            ( str.substr
                recv_input_4_1024
                (+
                    ( str.indexof recv_input_4_1024 " \r\n" (+ ( str.indexof recv_input_4_1024 " \r\n" 0) 1))
                    1)
                ( str.indexof
                    recv_input_4_1024
                    " \r\n"
                    (+ ( str.indexof recv_input_4_1024 " \r\n" (+ ( str.indexof recv_input_4_1024 " \r\n" 0) 1)) 1)
                )
            )
            10
            1014)))
        (check-sat)
        """

        recv_input = claripy.StringS("recv_input", 1024)
        constraints = []

        def field_sep_idx(s, start_idx=0):
            return claripy.StrIndexOf(s, claripy.StringV(" \r\n"), start_idx, 32)

        constraints.append(claripy.StrIndexOf(recv_input, claripy.StringV("\r\n\r\n"), 0, 32) < 0)
        sep_idx_1 = field_sep_idx(recv_input)
        sep_idx_2 = field_sep_idx(recv_input, start_idx=sep_idx_1 + 1)
        sep_idx_3 = field_sep_idx(recv_input, start_idx=sep_idx_2 + 1)
        sep_idx_4 = field_sep_idx(recv_input, start_idx=sep_idx_3 + 1)

        constraints.append(sep_idx_1 >= 0)
        constraints.append(sep_idx_2 >= 0)
        constraints.append(sep_idx_3 >= 0)

        sub_start = sep_idx_2 + 1
        sub_end = sep_idx_3

        sub_str = claripy.StrSubstr(recv_input, sub_start, sub_end)

        constraints.append(claripy.StrSubstr(sub_str, 10, 1014) == claripy.StringV("GET"))

        results = self._collect_generic_solver_test_data((recv_input,), constraints)
        self._generic_consistency_check(results)
        self._generic_congruency_check(results["solvers"], results)


if __name__ == "__main__":
    suite = unittest.TestLoader().loadTestsFromTestCase(SmtLibSolverTestCongruency)
    unittest.TextTestRunner(verbosity=2).run(suite)
