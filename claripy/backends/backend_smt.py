import logging

from pysmt.shortcuts import Symbol, String, StrConcat, Equals, NotEquals, \
                            StrSubstr, Int, StrLength, StrReplace, \
                            Bool, BV
from pysmt.typing import STRING

l = logging.getLogger("claripy.backends.backend_smt")

from . import BackendError, Backend

def _expr_to_smtlib(e):
    if e.is_symbol():
        return "(declare-const %s %s)" % (e.symbol_name(), e.symbol_type())
    else:
        return "(assert %s)" % e.to_smtlib()

def _exprs_to_smtlib(*exprs):
    return '\n'.join(_expr_to_smtlib(e) for e in exprs) + '\n'


class BackendSMT(Backend):
    def __init__(self):
        Backend.__init__(self)

        self.solver = None

        self._op_expr['StringV'] = self.StringV
        self._op_expr['StringS'] = self.StringS
        self._op_expr['BoolV'] = self.BoolV
        self._op_expr['BVV'] = self.BVV

        self._op_raw['__eq__'] = self._op_eq
        self._op_raw['__ne__'] = self._op_ne
        self._op_raw['StrConcat'] = self._op_raw_str_concat
        self._op_raw['Substr'] = self._op_raw_str_substr
        self._op_raw['StrLen'] = self._op_raw_str_strlen
        self._op_raw['StrReplace'] = self._op_raw_str_replace

    def register_solver(self, solver):
        self.solver = solver

    def _smtlib_exprs(self, extra_constraints=()):
        all_exprs = tuple(self.solver.get_assertions()) + tuple(extra_constraints)
        return _exprs_to_smtlib(*all_exprs)

    def _get_satisfiability_smt_script(self, extra_constraints=()):
        '''
        Returns a SMT script that declare all the symbols and constraint and checks
        their satisfiability (check-sat)
        '''
        smt_script = '(set-logic ALL)\n'
        smt_script += self._smtlib_exprs(extra_constraints)
        smt_script += '(check-sat)\n'
        return smt_script

    def _get_full_model_smt_script(self, extra_constraints=()):
        '''
        Returns a SMT script that declare all the symbols and constraint and checks
        their satisfiability (check-sat)
        '''
        smt_script = '(set-logic ALL)\n'
        smt_script += '(set-option :produce-models true)\n'
        smt_script += self._smtlib_exprs(extra_constraints)
        smt_script += '(check-sat)\n'
        smt_script += '(get-model)\n'
        return smt_script


    def StringV(self, ast):
        # TODO: check correct format
        # self._op_expr['StringV'] = self.StringV
        #       if format not correct throw exception BackError()
        content, _ = ast.args
        return String(content)

    def StringS(self, ast):
        # TODO: check correct format
        #       if format not correct throw exception BackError()
        name, _ = ast.args
        assertion = Symbol(name, STRING)
        self.solver.push(assertion)
        return assertion

    def BoolV(self, ast):
        return Bool(ast.is_true())

    def BVV(self, ast):
        val, size = ast.args
        return BV(val, size)

    def _op_raw_str_concat(self, *args):
        return StrConcat(args)

    def _op_raw_str_substr(self, *args):
        i, j, symb = args
        return StrSubstr(symb, Int(i), Int(j))

    def _op_raw_str_strlen(self, *args):
        return StrLength(args[0])

    def _op_raw_str_replace(self, *args):
        initial_str, pattern_to_replace, replacement_pattern = args
        return StrReplace(initial_str, pattern_to_replace, replacement_pattern)

    def _op_eq(self, *args):
        expr_left, expr_rigth = args
        # We emulate the integer through a bitvector but
        # since a constraint with the form (assert (= (str.len Symb_str) bit_vect))
        # is not valid we need to tranform the concrete vqalue of the bitvector in an integer
        #
        # TODO: implement logic for integer
        if expr_left.is_str_op() and expr_rigth.is_bv_constant():
            return Equals(expr_left, Int(expr_rigth.bv_signed_value()))
        elif expr_left.is_bv_constant() and expr_rigth.is_str_op():
            return Equals(expr_rigth, Int(expr_left.bv_signed_value())) 
        return Equals(expr_left, expr_rigth)

    def _op_ne(self, *args):
        expr_left, expr_rigth = args
        return NotEquals(expr_left, expr_rigth)

    def _satisfiable(self, extra_constraints=(), solver=None, model_callback=None):
        raise BackendError('Use a specialized backend for solving SMTLIB formatted constraints!')


from ..operations import backend_operations, backend_fp_operations
from .. import bv, fp, strings
from ..errors import UnsatError
