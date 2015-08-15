import logging
l = logging.getLogger("claripy.backends.backend_concrete")

import z3

from ..backend import BackendError, Backend

class BackendConcrete(Backend):
    def __init__(self):
        Backend.__init__(self)
        self._make_raw_ops(set(backend_operations) - { 'BitVec', 'If' }, op_module=bv)
        self._make_raw_ops(backend_fp_operations, op_module=fp)
        self._op_raw_result['BitVec'] = self._BitVec
        self._op_raw_result['If'] = self._If
        self._z_true = z3.BoolVal(True)
        self._z_false = z3.BoolVal(False)

    def _BitVec(self, name, size, result=None): #pylint:disable=W0613,R0201
        if result is None:
            l.debug("BackendConcrete can only handle BitVec when we are given a model")
            raise BackendError("BackendConcrete can only handle BitVec when we are given a model")
        if name not in result.model:
            l.debug("BackendConcrete needs variable %s in the model", name)
            raise BackendError("BackendConcrete needs variable %s in the model" % name)
        else:
            return result.model[name]

    def _If(self, b, t, f, result=None): #pylint:disable=no-self-use,unused-argument
        if not isinstance(b, bool):
            raise BackendError("BackendConcrete can't handle non-bool condition in If.")
        else:
            return t if b else f

    def _size(self, e, result=None):
        if type(e) in { bool, long, int }:
            return None
        elif type(e) in { bv.BVV }:
            return e.size()
        elif isinstance(e, fp.FPV):
            return e.sort.length
        else:
            raise BackendError("can't get size of type %s" % type(e))

    def _name(self, e, result=None): #pylint:disable=unused-argument,no-self-use
        return None

    def _identical(self, a, b, result=None):
        if type(a) is bv.BVV and type(b) is bv.BVV and a.size() != b.size():
            return False
        else:
            return a == b

    def _convert(self, a, result=None):
        if type(a) in { int, long, float, bool, str, bv.BVV, fp.FPV, fp.RM, fp.FSort }:
            return a

        if not hasattr(a, '__module__') or a.__module__ != 'z3':
            raise BackendError("BackendConcrete got an unsupported type %s" % a.__class__)

        #if _backend_z3 is None:
        #   raise BackendError("can't convert z3 expressions when z3 is not in use")

        try:
            #if hasattr(_backend_z3, '_lock'):
            #   _backend_z3._lock.acquire() #pylint:disable=no-member

            if hasattr(a, 'as_long'): return bv.BVV(a.as_long(), a.size())
            elif isinstance(a, z3.FPNumRef):
                # TODO: don't replicate this code in backend_z3.py
                # this is really imprecise
                fp_mantissa = float(a.significand())
                fp_exp = float(a.exponent())
                value = fp_mantissa * (2 ** fp_exp)

                ebits = a.ebits()
                sbits = a.sbits()
                sort = fp.FSort.from_params(ebits, sbits)

                return fp.FPV(value, sort)
            elif isinstance(a, z3.BoolRef) and a.eq(self._z_true): return True
            elif isinstance(a, z3.BoolRef) and a.eq(self._z_false): return False
            elif result is not None and a.num_args() == 0:
                name = a.decl().name()
                if name in result.model:
                    return result.model[name]
                else:
                    l.debug("returning 0 for %s (not in model)", name)
                    return bv.BVV(0, a.size())
            else:
                #import ipdb; ipdb.set_trace()
                #l.warning("TODO: support more complex non-symbolic expressions, maybe?")
                raise BackendError("TODO: support more complex non-symbolic expressions, maybe?")
        finally:
            pass
            #if hasattr(_backend_z3, '_lock'):
            #   _backend_z3._lock.release() #pylint:disable=no-member

    def _simplify(self, e):
        return e

    def abstract(self, e):
        if isinstance(e, bv.BVV):
            return BVI(e, length=e.size())
        elif isinstance(e, bool):
            return BoolI(e)
        elif isinstance(e, fp.FPV):
            return FPI(e)
        else:
            raise BackendError("Couldn't abstract object of type {}".format(type(e)))

    #
    # Evaluation functions
    #

    def _eval(self, expr, n, result=None, solver=None, extra_constraints=()):
        return (expr,)
    def _max(self, expr, result=None, solver=None, extra_constraints=()):
        return expr
    def _min(self, expr, result=None, solver=None, extra_constraints=()):
        return expr
    def _solution(self, expr, v, result=None, solver=None, extra_constraints=()):
        return self.convert(expr, result=result) == v

    def _is_true(self, e):
        return e == True
    def _is_false(self, e):
        return e == False
    def _has_true(self, e):
        return e == True
    def _has_false(self, e):
        return e == False

from ..operations import backend_operations, backend_fp_operations
from .. import bv, fp
#from .. import _backend_z3
from ..ast.bv import BVI
from ..ast.fp import FPI
from ..ast.bool import BoolI
