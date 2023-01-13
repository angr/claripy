import unittest
import claripy

from claripy import frontend_mixins, backend_manager
from claripy.backends.backend_smtlib import BackendSMTLibBase
from claripy.frontends.constrained_frontend import ConstrainedFrontend
from claripy.ast.strings import String

KEEP_TEST_PERFORMANT = True


class TestSMTLibBackend(unittest.TestCase):
    def get_solver(self):
        backend_manager.backends._register_backend(BackendSMTLibBase(), "smt", False, False)

        class SolverSMT(
            frontend_mixins.ConstraintFixerMixin,
            frontend_mixins.ConcreteHandlerMixin,
            frontend_mixins.ConstraintFilterMixin,
            frontend_mixins.ConstraintDeduplicatorMixin,
            frontend_mixins.EagerResolutionMixin,
            frontend_mixins.SMTLibScriptDumperMixin,
            ConstrainedFrontend,
        ):  # pylint:disable=abstract-method
            def __init__(self, *args, **kwargs):
                self._solver_backend = backend_manager.backends.smt
                super().__init__(*args, **kwargs)

        return SolverSMT()

    def test_concat(self):
        correct_script = """(set-logic ALL)
(declare-fun {0}symb_concat () String)
(assert (let ((.def_0 (str.++  "conc" {0}symb_concat))) (let ((.def_1 (= .def_0 "concrete"))) .def_1)))
(check-sat)
""".format(
            String.STRING_TYPE_IDENTIFIER
        )
        str_concrete = claripy.StringV("conc")
        str_symbol = claripy.StringS("symb_concat", 4, explicit_name=True)
        solver = self.get_solver()
        res = str_concrete + str_symbol
        solver.add(res == claripy.StringV("concrete"))
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_concat.smt2", "w") as dump_f:
        # dump_f.write(script)
        self.assertEqual(correct_script, script)

    def test_concat_simplification(self):
        correct_script = """(set-logic ALL)


(check-sat)
"""
        solver = self.get_solver()
        str_concrete = claripy.StringV("conc")
        res = str_concrete + str_concrete + str_concrete
        res2 = claripy.StrConcat(str_concrete, str_concrete) + str_concrete
        solver.add(res == res2)
        script = solver.get_smtlib_script_satisfiability()
        self.assertEqual(correct_script, script)

    def test_substr(self):
        correct_script = """(set-logic ALL)
(declare-fun {0}symb_subst () String)
(assert (let ((.def_0 (= ( str.substr {0}symb_subst 1 2) "on"))) .def_0))
(check-sat)
""".format(
            String.STRING_TYPE_IDENTIFIER
        )
        str_symbol = claripy.StringS("symb_subst", 4, explicit_name=True)
        solver = self.get_solver()
        res = claripy.StrSubstr(1, 2, str_symbol) == claripy.StringV("on")
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_substr.smt2", "w") as dump_f:
        # dump_f.write(script)
        self.assertEqual(correct_script, script)

    def test_substr_BV_concrete_index(self):
        correct_script = """(set-logic ALL)
(declare-fun {0}symb_subst () String)
(assert (let ((.def_0 (= ( str.substr {0}symb_subst 1 2) "on"))) .def_0))
(check-sat)
""".format(
            String.STRING_TYPE_IDENTIFIER
        )
        str_symbol = claripy.StringS("symb_subst", 4, explicit_name=True)
        solver = self.get_solver()
        bv1 = claripy.BVV(1, 32)
        bv2 = claripy.BVV(2, 32)
        res = claripy.StrSubstr(bv1, bv2, str_symbol) == claripy.StringV("on")
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_substr_bv_concrete.smt2", "w") as dump_f:
        # dump_f.write(script)
        self.assertEqual(correct_script, script)

    def test_substr_BV_symbolic_index(self):
        correct_script = """(set-logic ALL)
(declare-fun {0}symb_subst () String)
(declare-fun symb_subst_count () Int)
(declare-fun symb_subst_start_idx () Int)
(assert (let ((.def_0 (= ( str.substr {0}symb_subst symb_subst_start_idx symb_subst_count) "on"))) .def_0))
(check-sat)
""".format(
            String.STRING_TYPE_IDENTIFIER
        )
        str_symbol = claripy.StringS("symb_subst", 4, explicit_name=True)
        solver = self.get_solver()
        bv1 = claripy.BVS("symb_subst_start_idx", 32, explicit_name=True)
        bv2 = claripy.BVS("symb_subst_count", 32, explicit_name=True)
        res = claripy.StrSubstr(bv1, bv2, str_symbol) == claripy.StringV("on")
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_substr_bv_symbolic.smt2", "w") as dump_f:
        #     dump_f.write(script)
        self.assertEqual(correct_script, script)

    def test_substr_BV_mixed_index(self):
        correct_script = """(set-logic ALL)
(declare-fun {0}symb_subst () String)
(declare-fun symb_subst_start_idx () Int)
(assert (let ((.def_0 (= ( str.substr {0}symb_subst symb_subst_start_idx 2) "on"))) .def_0))
(check-sat)
""".format(
            String.STRING_TYPE_IDENTIFIER
        )
        str_symbol = claripy.StringS("symb_subst", 4, explicit_name=True)
        solver = self.get_solver()
        bv1 = claripy.BVS("symb_subst_start_idx", 32, explicit_name=True)
        bv2 = claripy.BVV(2, 32)
        res = claripy.StrSubstr(bv1, bv2, str_symbol) == claripy.StringV("on")
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_substr_bv_symbolic.smt2", "w") as dump_f:
        #     dump_f.write(script)
        self.assertEqual(correct_script, script)

    def test_substr_simplification(self):
        correct_script = """(set-logic ALL)


(check-sat)
"""
        str_concrete = claripy.StringV("concrete")
        solver = self.get_solver()
        solver.add(claripy.StrSubstr(1, 2, str_concrete) == claripy.StringV("on"))
        script = solver.get_smtlib_script_satisfiability()
        self.assertEqual(correct_script, script)

    def test_replace(self):
        correct_script = """(set-logic ALL)
(declare-fun {0}symb_repl () String)
(assert (let ((.def_0 (= ( str.replace {0}symb_repl "a" "b" ) "cbne"))) .def_0))
(check-sat)
""".format(
            String.STRING_TYPE_IDENTIFIER
        )
        str_to_replace_symb = claripy.StringS("symb_repl", 4, explicit_name=True)
        sub_str_to_repl = claripy.StringV("a")
        replacement = claripy.StringV("b")
        solver = self.get_solver()
        repl_stringa = claripy.StrReplace(str_to_replace_symb, sub_str_to_repl, replacement)
        solver.add(repl_stringa == claripy.StringV("cbne"))
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_replace.smt2", "w") as dump_f:
        # dump_f.write(script)
        self.assertEqual(correct_script, script)

    def test_replace_simplification(self):
        correct_script = """(set-logic ALL)


(check-sat)
"""
        str_to_replace = claripy.StringV("cane")
        sub_str_to_repl = claripy.StringV("a")
        replacement = claripy.StringV("b")
        repl_stringa = claripy.StrReplace(str_to_replace, sub_str_to_repl, replacement)
        solver = self.get_solver()
        solver.add(repl_stringa == claripy.StringV("cbne"))
        solver = self.get_solver()
        script = solver.get_smtlib_script_satisfiability()
        self.assertEqual(correct_script, script)

    def test_ne(self):
        correct_script = """(set-logic ALL)
(declare-fun {0}symb_ne () String)
(assert (let ((.def_0 (= {0}symb_ne "concrete"))) (let ((.def_1 (not .def_0))) .def_1)))
(check-sat)
""".format(
            String.STRING_TYPE_IDENTIFIER
        )
        str_symb = claripy.StringS("symb_ne", 12, explicit_name=True)
        solver = self.get_solver()
        solver.add(str_symb != claripy.StringV("concrete"))
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_ne.smt2", "w") as dump_f:
        #     dump_f.write(script)
        self.assertEqual(correct_script, script)

    def test_length(self):
        correct_script = """(set-logic ALL)
(declare-fun {0}symb_length () String)
(assert (let ((.def_0 (= (str.len {0}symb_length) 14))) .def_0))
(check-sat)
""".format(
            String.STRING_TYPE_IDENTIFIER
        )
        str_symb = claripy.StringS("symb_length", 12, explicit_name=True)
        solver = self.get_solver()
        # TODO: How do we want to dela with the size of a symbolic string?
        solver.add(claripy.StrLen(str_symb, 32) == 14)
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_length.smt2", "w") as dump_f:
        #     dump_f.write(script)
        self.assertEqual(correct_script, script)

    def test_length_simplification(self):
        correct_script = """(set-logic ALL)


(check-sat)
"""
        str_concrete = claripy.StringV("concrete")
        solver = self.get_solver()
        solver.add(claripy.StrLen(str_concrete, 32) == 8)
        script = solver.get_smtlib_script_satisfiability()
        self.assertEqual(correct_script, script)

    def test_or(self):
        correct_script = """(set-logic ALL)
(declare-fun {0}Symb_or () String)
(assert (let ((.def_0 (= {0}Symb_or "ciao"))) (let ((.def_1 (= {0}Symb_or "abc"))) (let ((.def_2 (or .def_1 .def_0))) .def_2))))
(check-sat)
""".format(
            String.STRING_TYPE_IDENTIFIER
        )
        str_symb = claripy.StringS("Symb_or", 4, explicit_name=True)
        solver = self.get_solver()
        res = claripy.Or((str_symb == claripy.StringV("abc")), (str_symb == claripy.StringV("ciao")))
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_or.smt2", "w") as dump_f:
        #     dump_f.write(script)
        self.assertEqual(correct_script, script)

    def test_lt_etc(self):
        correct_script = """(set-logic ALL)
(declare-fun {0}Symb_lt_test () String)
(assert (let ((.def_0 (<= (str.len {0}Symb_lt_test) 4))) .def_0))
(assert (let ((.def_0 (< (str.len {0}Symb_lt_test) 4))) .def_0))
(assert (let ((.def_0 (<= 4 (str.len {0}Symb_lt_test)))) .def_0))
(assert (let ((.def_0 (< 4 (str.len {0}Symb_lt_test)))) .def_0))
(check-sat)
""".format(
            String.STRING_TYPE_IDENTIFIER
        )
        str_symb = claripy.StringS("Symb_lt_test", 4, explicit_name=True)
        solver = self.get_solver()
        c1 = claripy.StrLen(str_symb, 32) <= 4
        c2 = claripy.StrLen(str_symb, 32) < 4
        c3 = claripy.StrLen(str_symb, 32) >= 4
        c4 = claripy.StrLen(str_symb, 32) > 4
        solver.add(c1)
        solver.add(c2)
        solver.add(c3)
        solver.add(c4)
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_lt_etc.smt2", "w") as dump_f:
        #     dump_f.write(script)
        self.assertEqual(correct_script, script)

    def test_contains(self):
        correct_script = """(set-logic ALL)
(declare-fun {0}symb_contains () String)
(assert ( str.contains {0}symb_contains "an"))
(check-sat)
""".format(
            String.STRING_TYPE_IDENTIFIER
        )
        str_symb = claripy.StringS("symb_contains", 4, explicit_name=True)
        res = claripy.StrContains(str_symb, claripy.StringV("an"))
        solver = self.get_solver()
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_contains.smt2", "w") as dump_f:
        #     dump_f.write(script)
        self.assertEqual(correct_script, script)

    def test_contains_simplification(self):
        correct_script = """(set-logic ALL)


(check-sat)
"""
        str_concrete = claripy.StringV("concrete")
        solver = self.get_solver()
        res = claripy.StrContains(str_concrete, claripy.StringV("nc"))
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        self.assertEqual(correct_script, script)

    def test_prefix(self):
        correct_script = """(set-logic ALL)
(declare-fun {0}symb_prefix () String)
(assert ( str.prefixof "an" {0}symb_prefix ))
(check-sat)
""".format(
            String.STRING_TYPE_IDENTIFIER
        )
        str_symb = claripy.StringS("symb_prefix", 4, explicit_name=True)
        res = claripy.StrPrefixOf(claripy.StringV("an"), str_symb)
        solver = self.get_solver()
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_prefix.smt2", "w") as dump_f:
        #     dump_f.write(script)
        self.assertEqual(correct_script, script)

    def test_suffix(self):
        correct_script = """(set-logic ALL)
(declare-fun {0}symb_suffix () String)
(assert ( str.suffixof "an" {0}symb_suffix ))
(check-sat)
""".format(
            String.STRING_TYPE_IDENTIFIER
        )
        str_symb = claripy.StringS("symb_suffix", 4, explicit_name=True)
        res = claripy.StrSuffixOf(claripy.StringV("an"), str_symb)
        solver = self.get_solver()
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_suffix.smt2", "w") as dump_f:
        #     dump_f.write(script)
        self.assertEqual(correct_script, script)

    def test_prefix_simplification(self):
        correct_script = """(set-logic ALL)


(check-sat)
"""
        str_concrete = claripy.StringV("concrete")
        solver = self.get_solver()
        res = claripy.StrPrefixOf(claripy.StringV("conc"), str_concrete)
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        self.assertEqual(correct_script, script)

    def test_suffix_simplification(self):
        correct_script = """(set-logic ALL)


(check-sat)
"""
        str_concrete = claripy.StringV("concrete")
        solver = self.get_solver()
        res = claripy.StrSuffixOf(claripy.StringV("rete"), str_concrete)
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        self.assertEqual(correct_script, script)

    def test_index_of(self):
        correct_script = """(set-logic ALL)
(declare-fun {0}symb_suffix () String)
(assert ( str.indexof {0}symb_suffix "an" 0 ))
(check-sat)
""".format(
            String.STRING_TYPE_IDENTIFIER
        )
        str_symb = claripy.StringS("symb_suffix", 4, explicit_name=True)
        res = claripy.StrIndexOf(str_symb, claripy.StringV("an"), 0, 32)
        solver = self.get_solver()
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_suffix.smt2", "w") as dump_f:
        #     dump_f.write(script)
        self.assertEqual(correct_script, script)

    def test_index_of_simplification(self):
        correct_script = """(set-logic ALL)


(check-sat)
"""
        str_concrete = claripy.StringV("concrete")
        solver = self.get_solver()
        res = claripy.StrIndexOf(str_concrete, claripy.StringV("rete"), 0, 32)
        solver.add(res == 4)
        script = solver.get_smtlib_script_satisfiability()
        self.assertEqual(correct_script, script)

    def test_index_of_symbolic_start_idx(self):
        correct_script = """(set-logic ALL)
(declare-fun {0}symb_index_of () String)
(declare-fun symb_start_idx () Int)
(assert (let ((.def_0 (< 32 symb_start_idx))) .def_0))
(assert (let ((.def_0 (< symb_start_idx 35))) .def_0))
(assert (let ((.def_0 (= ( str.indexof {0}symb_index_of "an" symb_start_idx ) 33))) .def_0))
(check-sat)
""".format(
            String.STRING_TYPE_IDENTIFIER
        )
        str_symb = claripy.StringS("symb_index_of", 4, explicit_name=True)
        start_idx = claripy.BVS("symb_start_idx", 32, explicit_name=True)

        solver = self.get_solver()

        solver.add(start_idx > 32)
        solver.add(start_idx < 35)
        res = claripy.StrIndexOf(str_symb, claripy.StringV("an"), start_idx, 32)

        solver.add(res == 33)
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_suffix.smt2", "w") as dump_f:
        #     dump_f.write(script)
        self.assertEqual(correct_script, script)

    def test_str_to_int(self):
        correct_script = """(set-logic ALL)
(declare-fun {0}symb_strtoint () String)
(assert (let ((.def_0 (= ( str.to.int {0}symb_strtoint ) 12))) .def_0))
(check-sat)
""".format(
            String.STRING_TYPE_IDENTIFIER
        )
        str_symb = claripy.StringS("symb_strtoint", 4, explicit_name=True)
        res = claripy.StrToInt(str_symb, 32)
        solver = self.get_solver()
        solver.add(res == 12)
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_strtoint.smt2", "w") as dump_f:
        #     dump_f.write(script)
        self.assertEqual(correct_script, script)

    def test_str_to_int_simplification(self):
        correct_script = """(set-logic ALL)


(check-sat)
"""
        str_concrete = claripy.StringV("12")
        solver = self.get_solver()
        res = claripy.StrToInt(str_concrete, 32)
        solver.add(res == 12)
        script = solver.get_smtlib_script_satisfiability()
        self.assertEqual(correct_script, script)

    def test_is_digit(self):
        correct_script = """(set-logic ALL)
(declare-fun STRING_symb_str_is_digit () String)
(assert (let ((.def_0 (= ( str.to.int STRING_symb_str_is_digit ) (- 1)))) (let ((.def_1 (not .def_0))) .def_1)))
(check-sat)
"""
        str_symb = claripy.StringS("symb_str_is_digit", 12, explicit_name=True)
        res = claripy.StrIsDigit(str_symb)
        solver = self.get_solver()
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        self.assertEqual(correct_script, script)

    def test_is_digit_simplification(self):
        correct_script = """(set-logic ALL)


(check-sat)
"""
        str_concrete = claripy.StringV("1")
        res = claripy.StrIsDigit(str_concrete)
        solver = self.get_solver()
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        self.assertEqual(correct_script, script)

    def test_int_to_str(self):
        correct_script = """(set-logic ALL)
(declare-fun symb_int () Int)
(assert (let ((.def_0 (= ( int.to.str symb_int ) "12"))) .def_0))
(check-sat)
"""
        int_symb = claripy.BVS("symb_int", 32, explicit_name=True)
        res = claripy.IntToStr(int_symb)
        solver = self.get_solver()
        solver.add(res == claripy.StringV("12"))
        script = solver.get_smtlib_script_satisfiability()
        self.assertEqual(correct_script, script)

    def test_int_to_str_simplification(self):
        correct_script = """(set-logic ALL)


(check-sat)
"""
        int_concrete = claripy.BVV(0xC, 32)
        res = claripy.IntToStr(int_concrete)
        solver = self.get_solver()
        solver.add(res == claripy.StringV("12"))
        script = solver.get_smtlib_script_satisfiability()
        self.assertEqual(correct_script, script)


if __name__ == "__main__":
    suite = unittest.TestLoader().loadTestsFromTestCase(TestSMTLibBackend)
    unittest.TextTestRunner(verbosity=2).run(suite)
