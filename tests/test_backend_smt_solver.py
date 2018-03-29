import unittest
from abc import abstractmethod
import abc

import claripy


class SmtLibSolverTest(unittest.TestCase):
    @abstractmethod
    def get_solver(self):
        raise NotImplementedError

    def test_concat(self):
        str_concrete = claripy.StringV("conc")
        str_symbol = claripy.StringS("symb_concat", 4, explicit_name=True)
        solver = self.get_solver()
        res = str_concrete + str_symbol
        solver.add(res == claripy.StringV("concrete"))
        self.assertTrue(solver.satisfiable())
        result = solver.eval(str_symbol, 2)
        self.assertEqual(1, len(result))
        self.assertEqual("rete", result[0])

        result = solver.eval_to_ast(str_symbol, 2)
        self.assertEqual([claripy.StringV("rete")], list(result))

    def test_concat_simplification(self):
        solver = self.get_solver()
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
        solver = self.get_solver()
        solver.add(claripy.StrSubstr(1, 2, str_symbol) == claripy.StringV('o'))
        self.assertTrue(solver.satisfiable())
        results = solver.eval(str_symbol, 2)
        self.assertEqual(len(results), 2)
        for s in results:
            self.assertTrue(s[1:2] == 'o')

    def test_substr_simplification(self):
        str_concrete = claripy.StringV("concrete")
        solver = self.get_solver()
        # TODO: Make sure that semantics of Substr match the ones of SMTLib substr
        solver.add(claripy.StrSubstr(1, 2, str_concrete) == claripy.StringV('on'))
        self.assertTrue(solver.satisfiable())
        result = solver.eval(str_concrete, 2)
        self.assertEqual(list(result), ["concrete"])

    def test_replace(self):
        str_to_replace_symb = claripy.StringS("symb_repl", 4, explicit_name=True)
        sub_str_to_repl = claripy.StringV("a")
        replacement = claripy.StringV("b")
        solver = self.get_solver()
        repl_stringa = claripy.StrReplace(str_to_replace_symb, sub_str_to_repl, replacement)
        solver.add(repl_stringa == claripy.StringV("cbne"))
        self.assertTrue(solver.satisfiable())

        result = solver.eval(repl_stringa, 2)
        self.assertEqual(list(result), ["cbne"])

        result = solver.eval(str_to_replace_symb, 2)
        self.assertEqual(set(result), {"cbne", "cane"})

    def test_replace_simplification(self):
        str_to_replace = claripy.StringV("cane")
        sub_str_to_repl = claripy.StringV("a")
        replacement = claripy.StringV("b")
        repl_stringa = claripy.StrReplace(str_to_replace, sub_str_to_repl, replacement)
        solver = self.get_solver()
        solver.add(repl_stringa == claripy.StringV("cbne"))

        self.assertTrue(solver.satisfiable())

        result = solver.eval(repl_stringa, 2)
        self.assertEqual(["cbne"], list(result))

        result = solver.eval(str_to_replace, 2)
        self.assertEqual(["cane"], list(result))

    def test_ne(self):
        str_symb = claripy.StringS("symb_ne", 12, explicit_name=True)
        solver = self.get_solver()
        solver.add(str_symb != claripy.StringV("concrete"))
        self.assertTrue(solver.satisfiable())

        result = solver.eval(str_symb, 20)
        self.assertTrue('concrete' not in result)

    def test_length(self):
        str_symb = claripy.StringS("symb_length", 12, explicit_name=True)
        solver = self.get_solver()
        # TODO: How do we want to deal with the size of a symbolic string?
        solver.add(claripy.StrLen(str_symb, 32) == 14)
        self.assertTrue(solver.satisfiable())

        result = solver.eval(str_symb, 20)
        for r in result:
            self.assertTrue(len(r) == 14)

    def test_length_simplification(self):
        str_concrete = claripy.StringV("concrete")
        solver = self.get_solver()
        solver.add(claripy.StrLen(str_concrete, 32) == 8)
        self.assertTrue(solver.satisfiable())

        result = solver.eval(str_concrete, 2)
        self.assertEqual(['concrete'], list(result))
        for r in result:
            self.assertTrue(len(r) == 8)


    def test_or(self):
        str_symb = claripy.StringS("Symb_or", 4, explicit_name=True)
        solver = self.get_solver()
        res = claripy.Or((str_symb == claripy.StringV("abc")),
                         (str_symb == claripy.StringV("ciao")))
        solver.add(res)
        self.assertTrue(solver.satisfiable())

        result = solver.eval(str_symb, 3)
        self.assertEqual({'ciao', 'abc'}, set(result))

    def test_lt_etc(self):
        str_symb = claripy.StringS("Symb_2", 4)
        solver = self.get_solver()
        c1 = claripy.StrLen(str_symb, 32) <= 4
        c2 = claripy.StrLen(str_symb, 32) < 4
        c3 = claripy.StrLen(str_symb, 32) >= 4
        c4 = claripy.StrLen(str_symb, 32) > 4
        solver.add(c1)
        solver.add(c2)
        solver.add(c3)
        solver.add(c4)
        self.assertFalse(solver.satisfiable())
