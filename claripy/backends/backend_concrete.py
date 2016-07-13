import logging
import operator
l = logging.getLogger("claripy.backends.backend_concrete")

from . import BackendError, Backend

class BackendConcrete(Backend):
    def __init__(self):
        Backend.__init__(self)
        self._make_raw_ops(set(backend_operations) - { 'If' }, op_module=bv)
        self._make_raw_ops(backend_fp_operations, op_module=fp)
        self._op_raw['If'] = self._If
        self._op_raw['BVV'] = self.BVV
        self._op_raw['FPV'] = self.FPV

        # reduceable
        self._op_raw['__add__'] = self._op_add
        self._op_raw['__sub__'] = self._op_sub
        self._op_raw['__mul__'] = self._op_mul
        self._op_raw['__or__'] = self._op_or
        self._op_raw['__xor__'] = self._op_xor
        self._op_raw['__and__'] = self._op_and

        self._cache_objects = False

    @staticmethod
    def BVV(value, size):
        if value is None:
            raise BackendError("can't handle empty BVVs")
        return bv.BVV(value, size)

    @staticmethod
    def FPV(op, sort):
        return fp.FPV(op, sort)

    @staticmethod
    def _op_add(*args):
        return reduce(operator.__add__, args)
    @staticmethod
    def _op_sub(*args):
        return reduce(operator.__sub__, args)
    @staticmethod
    def _op_mul(*args):
        return reduce(operator.__mul__, args)
    @staticmethod
    def _op_or(*args):
        return reduce(operator.__or__, args)
    @staticmethod
    def _op_xor(*args):
        return reduce(operator.__xor__, args)
    @staticmethod
    def _op_and(*args):
        return reduce(operator.__and__, args)

    def _If(self, b, t, f): #pylint:disable=no-self-use,unused-argument
        if not isinstance(b, bool):
            raise BackendError("BackendConcrete can't handle non-bool condition in If.")
        else:
            return t if b else f

    def _size(self, e):
        if type(e) in { bool, long, int }:
            return None
        elif type(e) in { bv.BVV }:
            return e.size()
        elif isinstance(e, fp.FPV):
            return e.sort.length
        else:
            raise BackendError("can't get size of type %s" % type(e))

    def _name(self, e): #pylint:disable=unused-argument,no-self-use
        return None

    def _identical(self, a, b):
        if type(a) is bv.BVV and type(b) is bv.BVV and a.size() != b.size():
            return False
        else:
            return a == b

    def _convert(self, a):
        if type(a) in { int, long, float, bool, str, bv.BVV, fp.FPV, fp.RM, fp.FSort }:
            return a
        raise BackendError("can't handle AST of type %s" % type(a))

    def _simplify(self, e):
        return e

    def _abstract(self, e): #pylint:disable=no-self-use
        if isinstance(e, bv.BVV):
            return BVV(e.value, e.size())
        elif isinstance(e, bool):
            return BoolV(e)
        elif isinstance(e, fp.FPV):
            return FPV(e.value, e.sort)
        else:
            raise BackendError("Couldn't abstract object of type {}".format(type(e)))

    def _cardinality(self, b):
        # if we got here, it's a cardinality of 1
        return 1

    #
    # Evaluation functions
    #

    @staticmethod
    def _to_primitive(expr):
        if type(expr) is bv.BVV:
            return expr.value
        elif type(expr) is fp.FPV:
            return expr.value
        elif type(expr) is bool:
            return expr
        elif type(expr) in (int, long):
            return expr

    def _eval(self, expr, n, extra_constraints=(), solver=None, model_callback=None):
        if not all(extra_constraints):
            raise UnsatError('concrete False constraint in extra_constraints')

        return (self._to_primitive(expr),)

    def _batch_eval(self, exprs, n, extra_constraints=(), solver=None, model_callback=None):
        if not all(extra_constraints):
            raise UnsatError('concrete False constraint in extra_constraints')

        return [ tuple(self._to_primitive(ex) for ex in exprs) ]

    def _max(self, expr, extra_constraints=(), solver=None, model_callback=None):
        if not all(extra_constraints):
            raise UnsatError('concrete False constraint in extra_constraints')
        return self._to_primitive(expr)

    def _min(self, expr, extra_constraints=(), solver=None, model_callback=None):
        if not all(extra_constraints):
            raise UnsatError('concrete False constraint in extra_constraints')
        return self._to_primitive(expr)

    def _solution(self, expr, v, extra_constraints=(), solver=None, model_callback=None):
        if not all(extra_constraints):
            raise UnsatError('concrete False constraint in extra_constraints')
        return self.convert(expr) == v

    #pylint:disable=singleton-comparison
    def _is_true(self, e, extra_constraints=(), solver=None, model_callback=None):
        return e == True
    def _is_false(self, e, extra_constraints=(), solver=None, model_callback=None):
        return e == False
    def _has_true(self, e, extra_constraints=(), solver=None, model_callback=None):
        return e == True
    def _has_false(self, e, extra_constraints=(), solver=None, model_callback=None):
        return e == False

from ..operations import backend_operations, backend_fp_operations
from .. import bv, fp
from ..ast.bv import BVV
from ..ast.fp import FPV
from ..ast.bool import BoolV
from ..errors import UnsatError
