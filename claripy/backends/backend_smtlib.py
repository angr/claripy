import logging

import pysmt
from pysmt.shortcuts import Symbol, String, StrConcat, Equals, NotEquals, \
    StrSubstr, Int, StrLength, StrReplace, \
    Bool, BV, Or, LT, LE, GT, GE, \
    StrContains, StrPrefixOf, StrSuffixOf, StrIndexOf, \
    StrToInt, BVAdd, BVSub, BVToNatural, Ite, EqualsOrIff, Minus, Plus

from pysmt.typing import STRING, BVType, INT, BOOL


l = logging.getLogger("claripy.backends.backend_smt")


from . import BackendError, Backend


class DeclareConst():
    def __init__(self, name, sort):
        self.name = name
        self.sort = sort

    def __repr__(self):
        return "(declare-const %s %r)" % (self.name, self.sort)


def _expr_to_smtlib(e, daggify=True):
    """
    Dump the symbol in its smt-format depending on its type

    :param e: symbol to dump

    :return string: smt-lib representation of the symbol
    """
    if e.is_symbol():
        return "(declare-fun %s %s)" % (e.symbol_name(), e.symbol_type().as_smtlib())
    else:
        return "(assert %s)" % e.to_smtlib(daggify=daggify)

def _exprs_to_smtlib(*exprs, **kwargs):
    """
    Dump all the variables and all the constraints in an smt-lib format

    :param exprs : List of variable declaration and constraints that have to be
             dumped in an smt-lib format

    :return string: smt-lib representation of the list of expressions 
    """
    return '\n'.join(_expr_to_smtlib(e, **kwargs) for e in exprs) + '\n'


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



class BackendSMTLibBase(Backend):
    def __init__(self, *args, **kwargs):
        self.daggify = kwargs.pop('daggify', True)
        Backend.__init__(self, *args, **kwargs)

        # ------------------- LEAF OPERATIONS ------------------- 
        self._op_expr['StringV'] = self.StringV
        self._op_expr['StringS'] = self.StringS
        self._op_expr['BoolV'] = self.BoolV
        self._op_expr['BoolS'] = self.BoolS
        self._op_expr['BVV'] = self.BVV
        self._op_expr['BVS'] = self.BVS

        # ------------------- BITVECTOR OPERATIONS -------------------
        # self._op_raw['Extract'] = self._op_raw_extract
        # self._op_raw['Concat'] = self._op_raw_concat
        self._op_raw['__add__'] = self._op_raw_add
        self._op_raw['__sub__'] = self._op_raw_sub

        # ------------------- GENERAL PURPOSE OPERATIONS ------------------- 
        self._op_raw['__eq__'] = self._op_raw_eq
        self._op_raw['__ne__'] = self._op_raw_ne
        self._op_raw['__lt__'] = self._op_raw_lt
        self._op_raw['__le__'] = self._op_raw_le
        self._op_raw['__gt__'] = self._op_raw_gt
        self._op_raw['__ge__'] = self._op_raw_ge
        self._op_raw['Or'] = self._op_raw_or
        self._op_raw['If'] = self._op_raw_if

        # ------------------- STRINGS OPERATIONS ------------------- 
        self._op_raw['StrConcat'] = self._op_raw_str_concat
        self._op_raw['StrSubstr'] = self._op_raw_str_substr
        self._op_raw['StrExtract'] = self._op_raw_str_extract
        self._op_raw['StrLen'] = self._op_raw_str_strlen
        self._op_raw['StrReplace'] = self._op_raw_str_replace
        self._op_raw["StrContains"] = self._op_raw_str_contains
        self._op_raw["StrPrefixOf"] = self._op_raw_str_prefixof
        self._op_raw["StrSuffixOf"] = self._op_raw_str_suffixof
        self._op_raw["StrIndexOf"] = self._op_raw_str_indexof
        self._op_raw["StrToInt"] = self._op_raw_str_strtoint

    def _smtlib_exprs(self, exprs):
        return _exprs_to_smtlib(*exprs, daggify=self.daggify)

    def _get_satisfiability_smt_script(self, constraints=(), variables=()):
        '''
        Returns a SMT script that declare all the symbols and constraint and checks
        their satisfiability (check-sat)

        :param extra-constraints: list of extra constraints that we want to evaluate only
                                 in the scope of this call
                                
        :return string: smt-lib representation of the script that checks the satisfiability
        '''
        smt_script = '(set-logic ALL)\n'
        smt_script += self._smtlib_exprs(variables)
        smt_script += self._smtlib_exprs(constraints)
        smt_script += '(check-sat)\n'
        return smt_script

    def _get_full_model_smt_script(self, constraints=(), variables=()):
        '''
        Returns a SMT script that declare all the symbols and constraint and checks
        their satisfiability (check-sat)

        :param extra-constraints: list of extra constraints that we want to evaluate only
                                 in the scope of this call

        :return string: smt-lib representation of the script that checks the satisfiability
        '''
        smt_script = '(set-logic ALL)\n'
        smt_script += '(set-option :produce-models true)\n'
        smt_script += self._smtlib_exprs(variables)
        smt_script += self._smtlib_exprs(constraints)
        smt_script += '(check-sat)\n'
        smt_script += '(get-model)\n'
        return smt_script

    def _get_all_vars_and_constraints(self, solver=None, e_c=(), e_v=()):
        all_csts = tuple(e_c) + (tuple(solver.constraints) if solver is not None else ())
        free_variables = set(e_v).union(*[c.get_free_variables() for c in all_csts])
        sorted_vars = sorted(free_variables, key=lambda s: s.symbol_name())
        return sorted_vars, all_csts

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
        return Bool(ast.args[0])

    def BoolS(self, ast):
        return Symbol(ast.args[0], BOOL)

    def BVV(self, ast):
        val, _ = ast.args
        if val & (1 << (ast.length - 1)):
            # negative
            val = -((1 << ast.length) - val)
        return Int(val)

    def BVS(self, ast):
        return Symbol(ast.args[0], INT) #BVType(ast.length))

    # ------------------- BITVECTOR OPERATIONS -------------------
    '''
    def _op_raw_extract(self, high, low, val):
        import ipdb; ipdb.set_trace()
        return BVExtract(val, start=low, end=high)

    def _op_raw_concat(self, left, right):
        import ipdb; ipdb.set_trace()
        return BVConcat(left, right)
    '''

    def _op_raw_add(self, *args):
        return Plus(*args)

    def _op_raw_sub(self, *args):
        return Minus(*args)

    # ------------------- GENERAL PURPOSE OPERATIONS -------------------

    def _op_raw_if(self, *args):
        return Ited(*args)

    def _op_raw_eq(self, *args):
        # We emulate the integer through a bitvector but
        # since a constraint with the form (assert (= (str.len Symb_str) bit_vect))
        # is not valid we need to tranform the concrete vqalue of the bitvector in an integer
        #
        # TODO: implement logic for integer
        return EqualsOrIff(*_normalize_arguments(*args))

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

    def _op_raw_if(self, *args):
        return Ite(*args)

    # ------------------- STRINGS OPERATIONS ------------------- 
    
    def _op_raw_str_concat(self, *args):
        return StrConcat(*args)

    def _op_raw_str_substr(self, *args):
        start_idx, count, symb = args
        start_idx_operand = start_idx
        count_operand = count
        # start_idx_operand = BVToNatural(start_idx) if start_idx.get_type().is_bv_type() else start_idx
        # count_operand = BVToNatural(count) if count.get_type().is_bv_type() else count
        return StrSubstr(symb, start_idx_operand, count_operand)

    def _op_raw_str_extract(self, *args):
        start_idx, count, symb = args
        return StrSubstr(symb, Int(start_idx), Int(count))

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

    def _op_raw_str_indexof(self, *args):
        input_string, substring, start, bitlength = args
        return StrIndexOf(input_string, substring, start)

    def _op_raw_str_strtoint(self, *args):
        input_string, _ = args
        return StrToInt(input_string)


from ..operations import backend_operations, backend_fp_operations
from .. import bv, fp, strings
from ..errors import UnsatError
