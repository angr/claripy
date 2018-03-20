import unittest
import claripy
from claripy import frontend_mixins, frontends, backend_manager, backends
from claripy.backends import BackendSMT_CVC4

backend_smt = backend_manager.backends._register_backend(BackendSMT_CVC4(), 'smt_cvc4', False, False)

class SolverSMT_CVC4(
    frontend_mixins.ConstraintFixerMixin,
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.ConstraintFilterMixin,
    frontend_mixins.ConstraintDeduplicatorMixin,
    frontend_mixins.EagerResolutionMixin,
    frontends.FullFrontend,
):
    def __init__(self, **kwargs):
        super(SolverSMT_CVC4, self).__init__(backends.smt_cvc4, **kwargs)


class TestStringOperation(unittest.TestCase):
    def test_concat(self):
        str_concrete = claripy.StringV("conc")
        str_symbol = claripy.StringS("symb_concat", 4, explicit_name=True)
        solver = SolverSMT_CVC4()
        res = str_concrete + str_symbol
        solver.add(res == claripy.StringV("concrete"))
        self.assertTrue(solver.satisfiable())
        result = solver.eval(str_symbol, 2)
        self.assertEqual(1, len(result))
        self.assertEqual("rete", result[0])

    def test_concat_simplification(self):
        solver = SolverSMT_CVC4()
        str_concrete = claripy.StringV("conc")
        res = str_concrete + str_concrete + str_concrete
        res2 = claripy.StrConcat(str_concrete, str_concrete)
        res3 = claripy.StrConcat(res2, str_concrete)
        solver.add(res == res3)
        self.assertTrue(solver.satisfiable())
        result = solver.eval(str_concrete, 2)
        self.assertEqual(["conc"], list(result))

    def test_substr(self):
        str_symbol = claripy.StringS("symb_subst", 4, explicit_name=True)
        solver = SolverSMT_CVC4()
        solver.add(str_symbol[1:2] == claripy.StringV('o'))
        self.assertTrue(solver.satisfiable())
        results = solver.eval(str_symbol, 2)
        self.assertEqual(len(results), 2)
        for s in results:
            self.assertTrue(s[1:2] == 'o')

    def test_substr_simplification(self):
        str_concrete = claripy.StringV("concrete")
        solver = SolverSMT_CVC4()
        solver.add(str_concrete[1:2] == claripy.StringV('o'))
        self.assertTrue(solver.satisfiable())
        result = solver.eval(str_concrete, 2)
        self.assertEqual(list(result), ["concrete"])

    def test_replace(self):
        str_to_replace_symb = claripy.StringS("symb_repl", 4, explicit_name=True)
        sub_str_to_repl = claripy.StringV("a")
        replacement = claripy.StringV("b")
        solver = SolverSMT_CVC4()
        repl_stringa = claripy.StrReplace(str_to_replace_symb, sub_str_to_repl, replacement)
        solver.add(repl_stringa == claripy.StringV("cbne"))
        self.assertTrue(solver.satisfiable())

        result = solver.eval(repl_stringa, 2)
        self.assertEqual(list(result), ["cbne"])

        result = solver.eval(str_to_replace_symb, 2)
        self.assertEqual(list(result), ["cane"])

    def test_replace_simplification(self):
        str_to_replace = claripy.StringV("cane")
        sub_str_to_repl = claripy.StringV("a")
        replacement = claripy.StringV("b")
        repl_stringa = claripy.StrReplace(str_to_replace, sub_str_to_repl, replacement)
        solver = SolverSMT_CVC4()
        solver.add(repl_stringa == claripy.StringV("cbne"))

        self.assertTrue(solver.satisfiable())

        result = solver.eval(repl_stringa, 2)
        self.assertEqual(["cbne"], list(result))

        result = solver.eval(str_to_replace, 2)
        self.assertEqual(["cane"], list(result))

    def test_ne(self):
        str_symb = claripy.StringS("symb_ne", 12, explicit_name=True)
        solver = SolverSMT_CVC4()
        solver.add(str_symb != claripy.StringV("concrete"))
        self.assertTrue(solver.satisfiable())

        result = solver.eval(str_symb, 100)
        self.assertTrue('concrete' not in result)

    def test_length(self):
        str_symb = claripy.StringS("symb_length", 12, explicit_name=True)
        solver = SolverSMT_CVC4()
        # TODO: How do we want to deal with the size of a symbolic string?
        solver.add(claripy.StrLen(str_symb) == 14)
        self.assertTrue(solver.satisfiable())

        result = solver.eval(str_symb, 100)
        for r in result:
            self.assertTrue(len(r) == 14)

    def test_length_simplification(self):
        str_concrete = claripy.StringV("concrete")
        solver = SolverSMT_CVC4()
        solver.add(claripy.StrLen(str_concrete) == 8)
        self.assertTrue(solver.satisfiable())

        result = solver.eval(str_concrete, 2)
        self.assertEqual(['concrete'], list(result))
        for r in result:
            self.assertTrue(len(r) == 8)


    def test_or(self):
        str_symb = claripy.StringS("Symb_or", 4, explicit_name=True)
        solver = SolverSMT_CVC4()
        res = claripy.Or((str_symb == claripy.StringV("abc")),
                         (str_symb == claripy.StringV("ciao")))
        solver.add(res)
        self.assertTrue(solver.satisfiable())

        result = solver.eval(str_symb, 3)
        self.assertEqual({'ciao', 'abc'}, set(result))

    def test_lt_etc(self):
        str_symb = claripy.StringS("Symb_2", 4)
        solver = SolverSMT_CVC4()
        c1 = claripy.StrLen(str_symb) <= 4
        c2 = claripy.StrLen(str_symb) < 4
        c3 = claripy.StrLen(str_symb) >= 4
        c4 = claripy.StrLen(str_symb) > 4
        solver.add(c1)
        solver.add(c2)
        solver.add(c3)
        solver.add(c4)
        self.assertFalse(solver.satisfiable())

if __name__ == "__main__":
    suite = unittest.TestLoader().loadTestsFromTestCase(TestStringOperation)
    unittest.TextTestRunner(verbosity=2).run(suite)
