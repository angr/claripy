# pylint: disable=missing-class-docstring,no-self-use
from __future__ import annotations

import unittest

import claripy

KEEP_TEST_PERFORMANT = True


class TestStrings(unittest.TestCase):
    def get_solver(self):
        return claripy.SolverStrings(backend=claripy.backends.z3)

    def test_concat(self):
        str_concrete = claripy.StringV("conc")
        str_symbol = claripy.StringS("symb_concat", explicit_name=True)
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
        str_symbol = claripy.StringS("symb_subst", explicit_name=True)
        solver = self.get_solver()
        solver.add(claripy.StrSubstr(1, 2, str_symbol) == claripy.StringV("o"))
        self.assertTrue(solver.satisfiable())
        results = solver.eval(str_symbol, 2 if KEEP_TEST_PERFORMANT else 100)
        self.assertEqual(len(results), 2 if KEEP_TEST_PERFORMANT else 100)
        for s in results:
            self.assertTrue(s[1:2] == "o")

    def test_substr_simplification(self):
        str_concrete = claripy.StringV("concrete")
        solver = self.get_solver()
        # TODO: Make sure that semantics of Substr match the ones of SMTLib substr
        solver.add(claripy.StrSubstr(1, 2, str_concrete) == claripy.StringV("on"))
        self.assertTrue(solver.satisfiable())
        result = solver.eval(str_concrete, 2)
        self.assertEqual(list(result), ["concrete"])

    def test_replace(self):
        str_to_replace_symb = claripy.StringS("symb_repl", explicit_name=True)
        sub_str_to_repl = claripy.StringV("a")
        replacement = claripy.StringV("b")
        solver = self.get_solver()
        repl_stringa = claripy.StrReplace(str_to_replace_symb, sub_str_to_repl, replacement)
        solver.add(repl_stringa == claripy.StringV("cbne"))
        self.assertTrue(solver.satisfiable())

        result = solver.eval(repl_stringa, 2)
        self.assertEqual(list(result), ["cbne"])

        result = solver.eval(str_to_replace_symb, 2 if KEEP_TEST_PERFORMANT else 100)
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
        str_symb = claripy.StringS("symb_ne", explicit_name=True)
        solver = self.get_solver()
        solver.add(str_symb != claripy.StringV("concrete"))
        self.assertTrue(solver.satisfiable())

        result = solver.eval(str_symb, 4 if KEEP_TEST_PERFORMANT else 100)
        self.assertTrue("concrete" not in result)

    def test_length(self):
        str_symb = claripy.StringS("symb_length", explicit_name=True)
        solver = self.get_solver()
        # TODO: How do we want to deal with the size of a symbolic string?
        solver.add(claripy.StrLen(str_symb) == 14)
        self.assertTrue(solver.satisfiable())

        result = solver.eval(str_symb, 4 if KEEP_TEST_PERFORMANT else 100)
        for r in result:
            self.assertTrue(len(r) == 14)

    def test_length_simplification(self):
        str_concrete = claripy.StringV("concrete")
        solver = self.get_solver()
        solver.add(claripy.StrLen(str_concrete) == 8)
        self.assertTrue(solver.satisfiable())

        result = solver.eval(str_concrete, 2)
        self.assertEqual(["concrete"], list(result))
        for r in result:
            self.assertTrue(len(r) == 8)

    def test_or(self):
        str_symb = claripy.StringS("Symb_or", explicit_name=True)
        solver = self.get_solver()
        res = claripy.Or((str_symb == claripy.StringV("abc")), (str_symb == claripy.StringV("ciao")))
        solver.add(res)
        self.assertTrue(solver.satisfiable())

        result = solver.eval(str_symb, 3 if KEEP_TEST_PERFORMANT else 100)
        self.assertEqual({"ciao", "abc"}, set(result))

    def test_lt_etc(self):
        str_symb = claripy.StringS("Symb_2")
        solver = self.get_solver()
        c1 = claripy.StrLen(str_symb) <= 4
        c2 = claripy.StrLen(str_symb) < 4
        c3 = claripy.StrLen(str_symb) >= 4
        c4 = claripy.StrLen(str_symb) > 4
        solver.add(c1)
        solver.add(c2)
        solver.add(c3)
        solver.add(c4)
        self.assertFalse(solver.satisfiable())

    def test_substr_BV_concrete_index(self):
        str_symbol = claripy.StringS("symb_subst", explicit_name=True)
        solver = self.get_solver()
        bv1 = claripy.BVV(1, 32)
        bv2 = claripy.BVV(2, 32)
        res = claripy.StrSubstr(bv1, bv2, str_symbol) == claripy.StringV("on")
        solver.add(res)
        self.assertTrue(solver.satisfiable())
        self.assertEqual("on", solver.eval(str_symbol, 1)[0][1:3])

    def test_substr_BV_symbolic_index(self):
        str_symbol = claripy.StringS("symb_subst", explicit_name=True)
        solver = self.get_solver()
        start = claripy.BVS("start_idx", 32)
        count = claripy.BVS("count", 32)
        res = claripy.StrSubstr(start, count, str_symbol) == claripy.StringV("on")
        solver.add(res)
        self.assertTrue(solver.satisfiable())
        self.assertEqual("on", solver.eval(str_symbol, 1, extra_constraints=(start == 0, count == 2))[0][0:2])
        self.assertEqual("on", solver.eval(str_symbol, 1, extra_constraints=(start == 1, count == 2))[0][1:3])
        self.assertEqual("on", solver.eval(str_symbol, 1, extra_constraints=(start == 2, count == 2))[0][2:4])

        self.assertEqual("on", solver.eval(str_symbol, 1, extra_constraints=(start == 2, count == 3))[0][2:4])
        self.assertEqual("on", solver.eval(str_symbol, 1, extra_constraints=(start == 2, count == 4))[0][2:4])

        self.assertEqual("on", solver.eval(str_symbol, 1, extra_constraints=(start == 0, count == 3))[0])
        self.assertEqual("on", solver.eval(str_symbol, 1, extra_constraints=(start == 1, count == 4))[0][1:])

    def test_substr_BV_mixed_index(self):
        str_symbol = claripy.StringS("symb_subst", explicit_name=True)
        solver = self.get_solver()
        start = claripy.BVS("symb_subst_start_idx", 32, explicit_name=True)
        count = claripy.BVV(2, 32)
        res = claripy.StrSubstr(start, count, str_symbol) == claripy.StringV("on")
        solver.add(res)
        self.assertTrue(solver.satisfiable())
        self.assertEqual("on", solver.eval(str_symbol, 1, extra_constraints=(start == 0,))[0][0:2])
        self.assertEqual("on", solver.eval(str_symbol, 1, extra_constraints=(start == 1,))[0][1:3])
        self.assertEqual("on", solver.eval(str_symbol, 1, extra_constraints=(start == 2,))[0][2:4])

    def test_contains(self):
        str_symb = claripy.StringS("symb_contains", explicit_name=True)
        res = claripy.StrContains(str_symb, claripy.StringV("an"))
        solver = self.get_solver()
        solver.add(res)
        self.assertTrue(solver.satisfiable())
        solutions = solver.eval(str_symb, 4 if KEEP_TEST_PERFORMANT else 100)
        for sol in solutions:
            self.assertTrue("an" in sol)

    def test_contains_simplification(self):
        str_concrete = claripy.StringV("concrete")
        solver = self.get_solver()
        res = claripy.StrContains(str_concrete, claripy.StringV("nc"))
        solver.add(res)
        self.assertTrue(solver.satisfiable())
        self.assertEqual((), tuple(solver.constraints))
        self.assertEqual(("concrete",), solver.eval(str_concrete, 2))
        self.assertEqual((True,), solver.eval(res, 2))

    def test_prefix(self):
        str_symb = claripy.StringS("symb_prefix", explicit_name=True)
        res = claripy.StrPrefixOf(claripy.StringV("an"), str_symb)
        solver = self.get_solver()
        solver.add(res)
        self.assertTrue(solver.satisfiable())

        solutions = solver.eval(str_symb, 4 if KEEP_TEST_PERFORMANT else 100)
        for sol in solutions:
            self.assertTrue(sol.startswith("an"))

    def test_suffix(self):
        str_symb = claripy.StringS("symb_suffix", explicit_name=True)
        res = claripy.StrSuffixOf(claripy.StringV("an"), str_symb)
        solver = self.get_solver()
        solver.add(res)
        self.assertTrue(solver.satisfiable())

        solutions = solver.eval(str_symb, 4 if KEEP_TEST_PERFORMANT else 100)
        for sol in solutions:
            self.assertTrue(sol.endswith("an"))

    def test_prefix_simplification(self):
        str_concrete = claripy.StringV("concrete")
        solver = self.get_solver()
        res = claripy.StrPrefixOf(claripy.StringV("conc"), str_concrete)
        solver.add(res)
        self.assertTrue(solver.satisfiable())
        self.assertEqual((), tuple(solver.constraints))
        self.assertEqual(("concrete",), solver.eval(str_concrete, 2))
        self.assertEqual((True,), solver.eval(res, 2))

    def test_suffix_simplification(self):
        str_concrete = claripy.StringV("concrete")
        solver = self.get_solver()
        res = claripy.StrSuffixOf(claripy.StringV("rete"), str_concrete)
        solver.add(res)
        self.assertTrue(solver.satisfiable())
        self.assertEqual((), tuple(solver.constraints))
        self.assertEqual(("concrete",), solver.eval(str_concrete, 2))
        self.assertEqual((True,), solver.eval(res, 2))

    def test_index_of(self):
        str_symb = claripy.StringS("symb_suffix", explicit_name=True)
        res = claripy.StrIndexOf(str_symb, claripy.StringV("an"), 0)
        solver = self.get_solver()

        target_idx = 4 if KEEP_TEST_PERFORMANT else 100
        solver.add(res == target_idx)
        self.assertTrue(solver.satisfiable())

        solutions = solver.eval(str_symb, 4 if KEEP_TEST_PERFORMANT else 100)
        for sol in solutions:
            self.assertEqual("an", sol[target_idx : target_idx + 2])

        self.assertEqual((target_idx,), solver.eval(res, 2))

    def test_index_of_simplification(self):
        str_concrete = claripy.StringV("concrete")
        solver = self.get_solver()
        res = claripy.StrIndexOf(str_concrete, claripy.StringV("rete"), 0)
        target_idx = 4 if KEEP_TEST_PERFORMANT else 100
        solver.add(res == target_idx)
        self.assertTrue(solver.satisfiable())
        self.assertEqual((), tuple(solver.constraints))
        self.assertEqual((target_idx,), solver.eval(res, 2))

    @unittest.skip("Usually hangs")
    def test_index_of_symbolic_start_idx(self):
        str_symb = claripy.StringS("symb_index_of", explicit_name=True)
        start_idx = claripy.BVS("symb_start_idx", 32, explicit_name=True)

        solver = self.get_solver()

        solver.add(start_idx > 32)
        solver.add(start_idx < 35)
        res = claripy.StrIndexOf(str_symb, claripy.StringV("an"), start_idx)

        solver.add(res != -1)
        solver.add(res < 38)
        self.assertTrue(solver.satisfiable())
        self.assertEqual({33, 34, 35, 36, 37}, set(solver.eval(res, 10)))

        strs = solver.eval(str_symb, 10 if KEEP_TEST_PERFORMANT else 100)
        for s in strs:
            self.assertTrue(32 < s.index("an") < 38)

    def test_str_to_int(self):
        str_symb = claripy.StringS("symb_strtoint", 4, explicit_name=True)
        res = claripy.StrToInt(str_symb)
        solver = self.get_solver()
        target_num = 12 if KEEP_TEST_PERFORMANT else 100000
        solver.add(res == target_num)
        self.assertTrue(solver.satisfiable())

        solutions = solver.eval(str_symb, 2 if KEEP_TEST_PERFORMANT else 1000000)
        for sol in solutions:
            self.assertTrue(int(sol) == target_num)

    def test_str_to_int_simplification(self):
        target_num = 12 if not KEEP_TEST_PERFORMANT else 1000000

        str_concrete = claripy.StringV(str(target_num))
        solver = self.get_solver()
        res = claripy.StrToInt(str_concrete)

        solver.add(res == target_num)
        self.assertTrue(solver.satisfiable())
        self.assertEqual((), tuple(solver.constraints))
        self.assertEqual((target_num,), solver.eval(res, 2))
