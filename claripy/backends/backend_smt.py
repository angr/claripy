import logging

from pysmt.shortcuts import Symbol, String, StrConcat, Equals, NotEquals, \
                            StrSubstr, Int, StrLength, StrReplace, \
                            Bool, BV
from pysmt.typing import STRING

l = logging.getLogger("claripy.backends.backend_smt")

from . import BackendError, Backend

def _expr_to_smtlib(e):
    """
    Dump the symbol in its smt-format depending on its type

    :param e: symbol to dump

    :return string: smt-lib representation of the symbol
    """
    if e.is_symbol():
        return "(declare-const %s %s)" % (e.symbol_name(), e.symbol_type())
    else:
        return "(assert %s)" % e.to_smtlib()

def _exprs_to_smtlib(*exprs):
    """
    Dump all the variables and all the constraints in an smt-lib format

    :param exprs : List of variable declaration and constraints that have to be
             dumped in an smt-lib format

    :return string: smt-lib representation of the list of expressions 
    """
    return '\n'.join(_expr_to_smtlib(e) for e in exprs) + '\n'


def _normalize_arguments(expr_left, expr_rigth):
    """
    Since we decided to emulate integer with bitvector, this method transform their
    concrete value (if any) in the corresponding integer
    """
    if expr_left.is_str_op() and expr_rigth.is_bv_constant():
        return expr_left, Int(expr_rigth.bv_signed_value())
    elif expr_left.is_bv_constant() and expr_rigth.is_str_op():
        return expr_rigth, Int(expr_left.bv_signed_value())
    return expr_left, expr_rigth



class BackendSMT(Backend):
    def __init__(self):
        Backend.__init__(self)

        # The assertions stack is inside tehe solver so we need the resference
        #  to it in order to retrieve variable declarations
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
        """
        Since the backend is shared among all the solver we need to register
        the correct solver for this backend so the backend can retieve the
        correct assertion_stack.

        This implementation is still wrong because if we register a new solver,
        All the other solvers wioll lose their assertion stacks

        :param solver : the appropriate solver for this backend
        """
        self.solver = solver

    def _smtlib_exprs(self, extra_constraints=()):
        """
        Return the smt-lib representation of the current context and constraints

        :param extra-constraints: list of extra constraints that we want to evaluate only
                                 in the scope of this call

        :return string: smt-lib representation of the list of expressions and variable declarations
        """
        all_exprs = tuple(self.solver.get_assertions()) + tuple(extra_constraints)
        return _exprs_to_smtlib(*all_exprs)

    def _get_satisfiability_smt_script(self, extra_constraints=()):
        '''
        Returns a SMT script that declare all the symbols and constraint and checks
        their satisfiability (check-sat)

        :param extra-constraints: list of extra constraints that we want to evaluate only
                                 in the scope of this call
                                
        :return string: smt-lib representation of the script that checks the satisfiability
        '''
        smt_script = '(set-logic ALL)\n'
        smt_script += self._smtlib_exprs(extra_constraints)
        smt_script += '(check-sat)\n'
        return smt_script

    def _get_full_model_smt_script(self, extra_constraints=()):
        '''
        Returns a SMT script that declare all the symbols and constraint and checks
        their satisfiability (check-sat)

        :param extra-constraints: list of extra constraints that we want to evaluate only
                                 in the scope of this call

        :return string: smt-lib representation of the script that checks the satisfiability
        '''
        smt_script = '(set-logic ALL)\n'
        smt_script += '(set-option :produce-models true)\n'
        smt_script += self._smtlib_exprs(extra_constraints)
        smt_script += '(check-sat)\n'
        smt_script += '(get-model)\n'
        return smt_script


    def StringV(self, ast):
        content, _ = ast.args
        return String(content)

    def StringS(self, ast):
        name, _ = ast.args
        # We need to keep track of new declarations
        # because when we dump the constraints we need to dump the
        # declaration as well
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
        # We emulate the integer through a bitvector but
        # since a constraint with the form (assert (= (str.len Symb_str) bit_vect))
        # is not valid we need to tranform the concrete vqalue of the bitvector in an integer
        #
        # TODO: implement logic for integer
        left_expr, right_expr = args
        norm_left_expr, norm_right_expr = _normalize_arguments(left_expr, right_expr)
        return Equals(norm_left_expr, norm_right_expr)

    def _op_ne(self, *args):
        # We emulate the integer through a bitvector but
        # since a constraint with the form (assert (= (str.len Symb_str) bit_vect))
        # is not valid we need to tranform the concrete vqalue of the bitvector in an integer
        #
        # TODO: implement logic for integer
        left_expr, right_expr = args
        norm_left_expr, norm_right_expr = _normalize_arguments(left_expr, right_expr)
        return NotEquals(norm_left_expr, norm_right_expr)

    def _satisfiable(self, extra_constraints=(), solver=None, model_callback=None):
        raise BackendError('Use a specialized backend for solving SMTLIB formatted constraints!')


from ..operations import backend_operations, backend_fp_operations
from .. import bv, fp, strings
from ..errors import UnsatError
