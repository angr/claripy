import logging

from pysmt.shortcuts import Symbol, String, StrConcat, Equals, NotEquals, \
                            StrSubstr, Int, StrLength, StrReplace, \
                            Bool, BV, Or, LT, LE, GT, GE, \
                            StrContains

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
    def __init__(self, *args, **kwargs):
        Backend.__init__(self, *args, **kwargs)

        # ------------------- LEAF OPERATIONS ------------------- 
        self._op_expr['StringV'] = self.StringV
        self._op_expr['StringS'] = self.StringS
        self._op_expr['BoolV'] = self.BoolV
        self._op_expr['BVV'] = self.BVV

        # ------------------- GENERAL PURPOSE OPERATIONS ------------------- 
        self._op_raw['__eq__'] = self._op_raw_eq
        self._op_raw['__ne__'] = self._op_raw_ne
        self._op_raw['__lt__'] = self._op_raw_lt
        self._op_raw['__le__'] = self._op_raw_le
        self._op_raw['__gt__'] = self._op_raw_gt
        self._op_raw['__ge__'] = self._op_raw_ge
        self._op_raw['Or'] = self._op_raw_or

        # ------------------- STRINGS OPERATIONS ------------------- 
        self._op_raw['StrConcat'] = self._op_raw_str_concat
        self._op_raw['Substr'] = self._op_raw_str_substr
        self._op_raw['StrLen'] = self._op_raw_str_strlen
        self._op_raw['StrReplace'] = self._op_raw_str_replace
        self._op_raw["StrContains"] = self._op_raw_str_contains


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

    def _satisfiable(self, extra_constraints=(), solver=None, model_callback=None):
        raise BackendError('Use a specialized backend for solving SMTLIB formatted constraints!')

    # ------------------- LEAF OPERATIONS ------------------- 

    def StringV(self, ast):
        content, _ = ast.args
        return String(content)

    def StringS(self, ast):
        # TODO: check correct format
        #       if format not correct throw exception BackError()
        name, _ = ast.args
        # We need to keep track of new declarations
        # because when we dump the constraints we need to dump the
        # declaration as well
        assertion = Symbol(name, STRING)
        return assertion

    def BoolV(self, ast):
        return Bool(ast.is_true())

    def BVV(self, ast):
        val, size = ast.args
        return BV(val, size)

    # ------------------- GENERAL PURPOSE OPERATIONS ------------------- 

    def _op_raw_eq(self, *args):
        # We emulate the integer through a bitvector but
        # since a constraint with the form (assert (= (str.len Symb_str) bit_vect))
        # is not valid we need to tranform the concrete vqalue of the bitvector in an integer
        #
        # TODO: implement logic for integer
        left_expr, right_expr = args
        norm_left_expr, norm_right_expr = _normalize_arguments(left_expr, right_expr)
        return Equals(norm_left_expr, norm_right_expr)

    def _op_raw_ne(self, *args):
        # We emulate the integer through a bitvector but
        # since a constraint with the form (assert (= (str.len Symb_str) bit_vect))
        # is not valid we need to tranform the concrete vqalue of the bitvector in an integer
        #
        # TODO: implement logic for integer
        left_expr, right_expr = args
        norm_left_expr, norm_right_expr = _normalize_arguments(left_expr, right_expr)
        return NotEquals(norm_left_expr, norm_right_expr)

    def _op_raw_lt(self, *args):
        # We emulate the integer through a bitvector but
        # since a constraint with the form (assert (= (str.len Symb_str) bit_vect))
        # is not valid we need to tranform the concrete vqalue of the bitvector in an integer
        #
        # TODO: implement logic for integer
        left_expr, right_expr = args
        norm_left_expr, norm_right_expr = _normalize_arguments(left_expr, right_expr)
        return LT(norm_left_expr, norm_right_expr)

    def _op_raw_le(self, *args):
        # We emulate the integer through a bitvector but
        # since a constraint with the form (assert (= (str.len Symb_str) bit_vect))
        # is not valid we need to tranform the concrete vqalue of the bitvector in an integer
        #
        # TODO: implement logic for integer
        left_expr, right_expr = args
        norm_left_expr, norm_right_expr = _normalize_arguments(left_expr, right_expr)
        return LE(norm_left_expr, norm_right_expr)

    def _op_raw_gt(self, *args):
        # We emulate the integer through a bitvector but
        # since a constraint with the form (assert (= (str.len Symb_str) bit_vect))
        # is not valid we need to tranform the concrete vqalue of the bitvector in an integer
        #
        # TODO: implement logic for integer
        left_expr, right_expr = args
        norm_left_expr, norm_right_expr = _normalize_arguments(left_expr, right_expr)
        return GT(norm_left_expr, norm_right_expr)

    def _op_raw_ge(self, *args):
        # We emulate the integer through a bitvector but
        # since a constraint with the form (assert (= (str.len Symb_str) bit_vect))
        # is not valid we need to tranform the concrete vqalue of the bitvector in an integer
        #
        # TODO: implement logic for integer
        left_expr, right_expr = args
        norm_left_expr, norm_right_expr = _normalize_arguments(left_expr, right_expr)
        return GE(norm_left_expr, norm_right_expr)

    def _op_raw_or(self, *args):
        return Or(*args)

    # ------------------- STRINGS OPERATIONS ------------------- 
    
    def _op_raw_str_concat(self, *args):
        return StrConcat(*args)

    def _op_raw_str_substr(self, *args):
        i, j, symb = args
        return StrSubstr(symb, Int(i), Int(j))

    def _op_raw_str_strlen(self, *args):
        return StrLength(args[0])

    def _op_raw_str_replace(self, *args):
        initial_str, pattern_to_replace, replacement_pattern = args
        return StrReplace(initial_str, pattern_to_replace, replacement_pattern)

    def _op_raw_str_contains(self, *args):
        input_string, substring = args
        return StrContains(input_string, substring)


from ..operations import backend_operations, backend_fp_operations
from .. import bv, fp, strings
from ..errors import UnsatError
