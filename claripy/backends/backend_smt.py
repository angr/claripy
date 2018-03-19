import logging

from pysmt.shortcuts import Symbol, String, StrConcat, Equals, NotEquals, \
                            StrSubstr, Int, StrLength, StrReplace, \
                            Bool, BV, Or, LT, LE, GT, GE, \
                            StrContains

from pysmt.typing import STRING


l = logging.getLogger("claripy.backends.backend_smt")


from . import BackendError, Backend


class DeclareConst():
    def __init__(self, name, sort):
        self.name = name
        self.sort = sort

    def __repr__(self):
        return "(declare-const %s %r)" % (self.name, self.sort)


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


    def _smtlib_exprs(self, constraints=()):
        """
        Return the smt-lib representation of the current context and constraints

        :param extra-constraints: list of extra constraints that we want to evaluate only
                                 in the scope of this call

        :return string: smt-lib representation of the list of expressions and variable declarations
        """
        free_variables = set().union(*[c.get_free_variables() for c in constraints])
        all_exprs = tuple(free_variables) +  tuple(constraints)
        return _exprs_to_smtlib(*all_exprs)

    def _get_satisfiability_smt_script(self, constraints=()):
        '''
        Returns a SMT script that declare all the symbols and constraint and checks
        their satisfiability (check-sat)

        :param extra-constraints: list of extra constraints that we want to evaluate only
                                 in the scope of this call
                                
        :return string: smt-lib representation of the script that checks the satisfiability
        '''
        smt_script = '(set-logic ALL)\n'
        smt_script += self._smtlib_exprs(constraints)
        smt_script += '(check-sat)\n'
        return smt_script

    def _get_full_model_smt_script(self, constraints=()):
        '''
        Returns a SMT script that declare all the symbols and constraint and checks
        their satisfiability (check-sat)

        :param extra-constraints: list of extra constraints that we want to evaluate only
                                 in the scope of this call

        :return string: smt-lib representation of the script that checks the satisfiability
        '''
        smt_script = '(set-logic ALL)\n'
        smt_script += '(set-option :produce-models true)\n'
        smt_script += self._smtlib_exprs(constraints)
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
        return Symbol(name, STRING)

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
        return Equals(*_normalize_arguments(*args))

    def _op_raw_ne(self, *args):
        # We emulate the integer through a bitvector but
        # since a constraint with the form (assert (= (str.len Symb_str) bit_vect))
        # is not valid we need to tranform the concrete vqalue of the bitvector in an integer
        #
        # TODO: implement logic for integer
        return NotEquals(*_normalize_arguments(*args))

    def _op_raw_lt(self, *args):
        # We emulate the integer through a bitvector but
        # since a constraint with the form (assert (= (str.len Symb_str) bit_vect))
        # is not valid we need to tranform the concrete vqalue of the bitvector in an integer
        #
        # TODO: implement logic for integer
        return LT(*_normalize_arguments(*args))

    def _op_raw_le(self, *args):
        # We emulate the integer through a bitvector but
        # since a constraint with the form (assert (= (str.len Symb_str) bit_vect))
        # is not valid we need to tranform the concrete vqalue of the bitvector in an integer
        #
        # TODO: implement logic for integer
        return LE(*_normalize_arguments(*args))

    def _op_raw_gt(self, *args):
        # We emulate the integer through a bitvector but
        # since a constraint with the form (assert (= (str.len Symb_str) bit_vect))
        # is not valid we need to tranform the concrete vqalue of the bitvector in an integer
        #
        # TODO: implement logic for integer
        return GT(*_normalize_arguments(*args))

    def _op_raw_ge(self, *args):
        # We emulate the integer through a bitvector but
        # since a constraint with the form (assert (= (str.len Symb_str) bit_vect))
        # is not valid we need to tranform the concrete vqalue of the bitvector in an integer
        #
        # TODO: implement logic for integer
        return GE(*_normalize_arguments(*args))

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

    # def _identical(self, a, b):
    #     if type(a) is bv.BVV and type(b) is bv.BVV and a.size() != b.size():
    #         return False
    #     else:
    #         return a == b

    # def _convert(self, a):
    #     if isinstance(a, (numbers.Number, bv.BVV, fp.FPV, fp.RM, fp.FSort, strings.StringV)):
    #         return a
    #     raise BackendError("can't handle AST of type %s" % type(a))

    # def _simplify(self, e):
    #     return e

    # def _abstract(self, e): #pylint:disable=no-self-use
    #     if isinstance(e, bv.BVV):
    #         return BVV(e.value, e.size())
    #     elif isinstance(e, bool):
    #         return BoolV(e)
    #     elif isinstance(e, fp.FPV):
    #         return FPV(e.value, e.sort)
    #     else:
    #         raise BackendError("Couldn't abstract object of type {}".format(type(e)))

    # def _cardinality(self, b):
    #     # if we got here, it's a cardinality of 1
    #     return 1

    # #
    # # Evaluation functions
    # #

    # @staticmethod
    # def _to_primitive(expr):
    #     if isinstance(expr, bv.BVV):
    #         return expr.value
    #     if isinstance(expr, fp.FPV):
    #         return expr.value
    #     if isinstance(expr, bool):
    #         return expr
    #     if isinstance(expr, numbers.Number):
    #         return expr

    # def _eval(self, expr, n, extra_constraints=(), solver=None, model_callback=None):
    #     if not all(extra_constraints):
    #         raise UnsatError('concrete False constraint in extra_constraints')

    #     return (self._to_primitive(expr),)

    # def _batch_eval(self, exprs, n, extra_constraints=(), solver=None, model_callback=None):
    #     if not all(extra_constraints):
    #         raise UnsatError('concrete False constraint in extra_constraints')

    #     return [ tuple(self._to_primitive(ex) for ex in exprs) ]

    # def _max(self, expr, extra_constraints=(), solver=None, model_callback=None):
    #     if not all(extra_constraints):
    #         raise UnsatError('concrete False constraint in extra_constraints')
    #     return self._to_primitive(expr)

    # def _min(self, expr, extra_constraints=(), solver=None, model_callback=None):
    #     if not all(extra_constraints):
    #         raise UnsatError('concrete False constraint in extra_constraints')
    #     return self._to_primitive(expr)

    # def _solution(self, expr, v, extra_constraints=(), solver=None, model_callback=None):
    #     if not all(extra_constraints):
    #         raise UnsatError('concrete False constraint in extra_constraints')
    #     return self.convert(expr) == v

    # #pylint:disable=singleton-comparison
    # def _is_true(self, e, extra_constraints=(), solver=None, model_callback=None):
    #     return e == True
    # def _is_false(self, e, extra_constraints=(), solver=None, model_callback=None):
    #     return e == False
    # def _has_true(self, e, extra_constraints=(), solver=None, model_callback=None):
    #     return e == True
    # def _has_false(self, e, extra_constraints=(), solver=None, model_callback=None):
    #     return e == False

from ..operations import backend_operations, backend_fp_operations
from .. import bv, fp, strings
from ..errors import UnsatError
