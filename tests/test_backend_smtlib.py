import unittest
import claripy


class TestStringOperation(unittest.TestCase):

    def test_concat(self):
        correct_script = '''
        (declare-const symb_concat String)
        (assert (let ((.def_0 (str.++  "conc" symb_concat))) (let ((.def_1 (= .def_0 "concrete"))) .def_1)))
        (check-sat)'
        '''
        str_concrete = claripy.StringV("conc")
        str_symbol = claripy.StringS("symb_concat", 4, explicit_name=True)
        solver = claripy.SolverSMT()
        res = str_concrete + str_symbol
        solver.add(res == claripy.StringV("concrete"))
        script = solver.satisfiable()
        # with open("dump_concat.smt2", "w") as dump_f:
            # dump_f.write(script)
        self.assertTrue(correct_script, script)

    def test_concat_simplification(self):
        solver = claripy.SolverSMT()
        str_concrete = claripy.StringV("conc")
        res = str_concrete + str_concrete + str_concrete
        res2 = claripy.StrConcat(str_concrete, str_concrete) + str_concrete
        solver.add(res == res2)
        script = solver.satisfiable()
        self.assertEqual(script, '(check-sat)\n')

    def test_substr(self):
        correct_script ='''
        (declare-const symb_subst String)
        (assert (let ((.def_0 (= ( str.substr symb_subst 1 2) "o"))) .def_0))
        (check-sat)'
        '''
        str_symbol = claripy.StringS("symb_subst", 4, explicit_name=True)
        solver = claripy.SolverSMT()
        solver.add(str_symbol[1:2] == claripy.StringV('o'))
        script = solver.satisfiable()
        # with open("dump_substr.smt2", "w") as dump_f:
            # dump_f.write(script)
        self.assertTrue(correct_script, script)

    def test_substr_simplification(self):
        str_concrete = claripy.StringV("concrete")
        solver = claripy.SolverSMT()
        solver.add(str_concrete[1:2] == claripy.StringV('o'))
        script = solver.satisfiable()
        self.assertEqual(script, '(check-sat)\n')

    def test_replace(self):
        correct_script = '''
        (declare-const symb_repl String)
        (assert (let ((.def_0 (= ( str.replace symb_repl "a" "b" ) "cbne"))) .def_0))
        (check-sat)'
        '''
        str_to_replace_symb = claripy.StringS("symb_repl", 4, explicit_name=True)
        sub_str_to_repl = claripy.StringV("a")
        replacement = claripy.StringV("b")
        solver = claripy.SolverSMT()
        repl_stringa = claripy.StrReplace(str_to_replace_symb, sub_str_to_repl, replacement)
        solver.add(repl_stringa == claripy.StringV("cbne"))
        script = solver.satisfiable()
        # with open("dump_replace.smt2", "w") as dump_f:
            # dump_f.write(script)
        self.assertTrue(correct_script, script)

    def test_replace_simplification(self):
        str_to_replace = claripy.StringV("cane")
        sub_str_to_repl = claripy.StringV("a")
        replacement = claripy.StringV("b")
        repl_stringa = claripy.StrReplace(str_to_replace, sub_str_to_repl, replacement)
        solver = claripy.SolverSMT()
        solver.add(repl_stringa == claripy.StringV("cbne"))
        solver = claripy.SolverSMT()
        script = solver.satisfiable()
        self.assertEqual(script, '(check-sat)\n')

    def test_ne(self):
        correct_script = '''
        (declare-const symb_ne String)
        (assert (let ((.def_0 (= symb_ne "concrete"))) (let ((.def_1 (not .def_0))) .def_1)))
        (check-sat)
        '''
        str_symb = claripy.StringS("symb_ne", 12, explicit_name=True)
        solver = claripy.SolverSMT()
        solver.add(str_symb != claripy.StringV("concrete"))
        script = solver.satisfiable()
        # with open("dump_ne.smt2", "w") as dump_f:
        #     dump_f.write(script)
        self.assertTrue(correct_script, script)

    def test_length(self):
        correct_script = '''
        (declare-const symb_length String)
        (assert (let ((.def_0 (= (str.len symb_length) 14))) .def_0))
        (check-sat)
        '''
        str_symb = claripy.StringS("symb_length", 12, explicit_name=True)
        solver = claripy.SolverSMT()
        # TODO: How do we want to dela with the size of a symbolic string?
        solver.add(claripy.StrLen(str_symb) == 14)
        script = solver.satisfiable()
        # with open("dump_length.smt2", "w") as dump_f:
        #     dump_f.write(script)
        self.assertTrue(correct_script, script)

    def test_length_simplification(self):
        str_concrete = claripy.StringV("concrete")
        solver = claripy.SolverSMT()
        solver.add(claripy.StrLen(str_concrete) == 8)
        script = solver.satisfiable()
        self.assertEqual(script, '(check-sat)\n')

    def test_or(self):
        correct_script = '''(set-logic ALL)
(declare-const Symb_or String)
(assert (let ((.def_0 (= Symb_or "ciao"))) (let ((.def_1 (= Symb_or "abc"))) (let ((.def_2 (or .def_1 .def_0))) .def_2))))
(check-sat)
'''
        str_symb = claripy.StringS("Symb_or", 4, explicit_name=True)
        solver = SolverSMT()
        res = claripy.Or((str_symb == claripy.StringV("abc")),
                         (str_symb == claripy.StringV("ciao")))
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_or.smt2", "w") as dump_f:
        #     dump_f.write(script)
        self.assertEqual(correct_script, script)

    def test_lt_etc(self):
        correct_script = '''(set-logic ALL)
(declare-const Symb_2_0_4 String)
(assert (let ((.def_0 (<= (str.len Symb_2_0_4) 4))) .def_0))
(assert (let ((.def_0 (< (str.len Symb_2_0_4) 4))) .def_0))
(assert (let ((.def_0 (<= 4 (str.len Symb_2_0_4)))) .def_0))
(assert (let ((.def_0 (< 4 (str.len Symb_2_0_4)))) .def_0))
(check-sat)
'''
        str_symb = claripy.StringS("Symb_2", 4)
        solver = SolverSMT()
        c1 = claripy.StrLen(str_symb) <= 4
        c2 = claripy.StrLen(str_symb) < 4
        c3 = claripy.StrLen(str_symb) >= 4
        c4 = claripy.StrLen(str_symb) > 4
        solver.add(c1)
        solver.add(c2)
        solver.add(c3)
        solver.add(c4)
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_lt_etc.smt2", "w") as dump_f:
        #     dump_f.write(script)
        self.assertEqual(correct_script, script)


    def test_contains(self):
        correct_script = '''(set-logic ALL)
(declare-const symb_contains String)
(assert ( str.contains symb_contains "an"))
(check-sat)
'''
        str_symb = claripy.StringS("symb_contains", 4, explicit_name=True)
        res = claripy.StrContains(str_symb, claripy.StringV("an"))
        solver = SolverSMT()
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_contains.smt2", "w") as dump_f:
        #     dump_f.write(script)
        self.assertEqual(correct_script, script)

    def test_contains_simplification(self):
        correct_script = '''(set-logic ALL)

(check-sat)
'''
        str_concrete = claripy.StringV("concrete")
        solver = SolverSMT()
        res = claripy.StrContains(str_concrete, claripy.StringV("nc"))
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        self.assertEqual(correct_script, script)


    def test_prefix(self):
        correct_script = '''(set-logic ALL)
(declare-const symb_prefix String)
(assert ( str.prefixof "an" symb_prefix ))
(check-sat)
'''
        str_symb = claripy.StringS("symb_prefix", 4, explicit_name=True)
        res = claripy.StrPrefixOf(claripy.StringV("an"), str_symb)
        solver = SolverSMT()
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_prefix.smt2", "w") as dump_f:
        #     dump_f.write(script)
        self.assertEqual(correct_script, script)

    def test_suffix(self):
        correct_script = '''(set-logic ALL)
(declare-const symb_suffix String)
(assert ( str.suffixof "an" symb_suffix ))
(check-sat)
'''
        str_symb = claripy.StringS("symb_suffix", 4, explicit_name=True)
        res = claripy.StrSuffixOf(claripy.StringV("an"), str_symb)
        solver = SolverSMT()
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_suffix.smt2", "w") as dump_f:
        #     dump_f.write(script)
        self.assertEqual(correct_script, script)

    def test_prefix_simplification(self):
        correct_script = '''(set-logic ALL)

(check-sat)
'''
        str_concrete = claripy.StringV("concrete")
        solver = SolverSMT()
        res = claripy.StrPrefixOf(claripy.StringV("conc"), str_concrete)
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        self.assertEqual(correct_script, script)

    def test_suffix_simplification(self):
        correct_script = '''(set-logic ALL)

(check-sat)
'''
        str_concrete = claripy.StringV("concrete")
        solver = SolverSMT()
        res = claripy.StrSuffixOf(claripy.StringV("rete"), str_concrete)
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        self.assertEqual(correct_script, script)

    def test_index_of(self):
        correct_script = '''(set-logic ALL)
(declare-const symb_suffix String)
(assert ( str.indexof symb_suffix "an" 0 ))
(check-sat)
'''
        str_symb = claripy.StringS("symb_suffix", 4, explicit_name=True)
        res = claripy.StrIndexOf(str_symb, claripy.StringV("an"), 32)
        solver = SolverSMT()
        solver.add(res)
        script = solver.get_smtlib_script_satisfiability()
        # with open("dump_suffix.smt2", "w") as dump_f:
        #     dump_f.write(script)
        self.assertEqual(correct_script, script)

    def test_index_of_simplification(self):
        correct_script = '''(set-logic ALL)

(check-sat)
'''
        str_concrete = claripy.StringV("concrete")
        solver = SolverSMT()
        res = claripy.StrIndexOf(str_concrete, claripy.StringV("rete"), 32)
        solver.add(res == 4)
        script = solver.get_smtlib_script_satisfiability()
        self.assertEqual(correct_script, script)

if __name__ == "__main__":
    suite = unittest.TestLoader().loadTestsFromTestCase(TestStringOperation)
    unittest.TextTestRunner(verbosity=2).run(suite)

# # # --------------- LENGTH EXAMPLE ----------------

# # length = claripy.String.Length(str_concrete)
# # length_symb = claripy.String.Length(str_symbol)
# # solverSMT.add(length == claripy.StringV('a')) solverSMT.add(str_symbol[1:2] == claripy.StringV('a')) solverSMT.add(len(str_concrete) == 4)
# # ipdb.set_trace()
