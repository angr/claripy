#!/usr/bin/env python

import claripy
import ipdb
from IPython import embed
import unittest

str_concrete = claripy.StringV("conc")
str_symbol = claripy.StringS("symb", 4)

solverSMT = claripy.SolverSMT()
solverz3 = claripy.Solver()


class TestStringOperation(unittest.TestCase):

    def test_concat(self):
        correct_script ='''
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
        res2 = claripy.StrConcat(str_concrete, str_concrete, str_concrete)
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
        solver = claripy.SolverSMT()
        solver.add(str_concrete[1:2] == claripy.StringV('o'))
        script = solver.satisfiable()
        self.assertEqual(script, '(check-sat)\n')

    def test_replace(self):
        correct_script ='''
        (declare-const symb_repl String)
        (assert (let ((.def_0 (= ( str.replace symb_repl "a" "b" ) "cbne"))) .def_0))
        (check-sat)'
        '''
        str_to_replace_symb = claripy.StringS("symb_repl", 4, explicit_name=True)
        sub_str_to_repl = claripy.StringV("a")
        replacement = claripy.StringV("b")
        solver = claripy.SolverSMT()
        repl_stringa = claripy.StrReplace(str_to_replace_symb, sub_str_to_repl, replacement)
        solverSMT.add(repl_stringa == claripy.StringV("cbne"))
        script = solver.satisfiable()
        # with open("dump_replace.smt2", "w") as dump_f:
            # dump_f.write(script)
        self.assertTrue(correct_script, script)

    def test_replace_simplification(self):
        str_to_replace = claripy.StringV("cane")
        sub_str_to_repl = claripy.StringV("a")
        replacement = claripy.StringV("b")
        repl_stringa = claripy.StrReplace(str_to_replace, sub_str_to_repl, replacement)
        solverSMT.add(repl_stringa == claripy.StringV("cbne"))
        solver = claripy.SolverSMT()
        script = solver.satisfiable()
        self.assertEqual(script, '(check-sat)\n')

    def test_ne(self):
        correct_script='''
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


    # def test_length(self):
    #     str_concrete = claripy.StringV("concrete")
    #     length_concrete = claripy.StrLen(str_concrete)
    #     str_symb = claripy.StringS("symb_len", 4, explicit_name=True)
    #     length = claripy.StrLen(str_concrete)
    #     solver = claripy.SolverSMT()
    #     import ipdb; ipdb.set_trace()
    #     constr = length == claripy.Int(8)
    #     solver.add(length == 8)

    # def test_or(self):
    #     str_concrete = claripy.StringV("ciao")
    #     str_symb = claripy.StringS("Symb_2", 4)
    #     solver = claripy.SolverSMT()
    #     res = claripy.Or(str_symb == , str_concrete)

    #     import ipdb; ipdb.set_trace()
        # solver.add((res or claripy.StringS("symb3", 8)) == (claripy.StringV("ciaociao")))




if __name__ == "__main__":
    suite = unittest.TestLoader().loadTestsFromTestCase(TestStringOperation)
    unittest.TextTestRunner(verbosity=2).run(suite)

# # # --------------- LENGTH EXAMPLE ----------------

# # length = claripy.String.Length(str_concrete)
# # length_symb = claripy.String.Length(str_symbol)
# # solverSMT.add(length == claripy.StringV('a')) solverSMT.add(str_symbol[1:2] == claripy.StringV('a')) solverSMT.add(len(str_concrete) == 4)
# # ipdb.set_trace()
