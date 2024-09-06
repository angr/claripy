from __future__ import annotations

import functools
import logging
import numbers
import operator
from functools import reduce

from claripy.ast.base import Base
from claripy.backends.backend import Backend
from claripy.balancer import Balancer
from claripy.errors import BackendError
from claripy.operations import backend_operations_vsa_compliant, expression_set_operations
from claripy.vsa import (
    BoolResult,
    CreateStridedInterval,
    DiscreteStridedIntervalSet,
    FalseResult,
    RegionAnnotation,
    StridedInterval,
    TrueResult,
    ValueSet,
)

l = logging.getLogger("claripy.backends.backend_vsa")


def arg_filter(f):
    @functools.wraps(f)
    def filter_(*args):
        if isinstance(args[0], numbers.Number):
            raise BackendError(f"Unsupported argument type {type(args[0])}")
        return f(*args)

    return filter_


def normalize_arg_order(f):
    @functools.wraps(f)
    def normalizer(*args):
        if len(args) != 2:
            raise BackendError("Unsupported arguments number %d" % len(args))

        if not isinstance(args[0], StridedInterval | DiscreteStridedIntervalSet | ValueSet):
            if not isinstance(args[1], StridedInterval | DiscreteStridedIntervalSet | ValueSet):
                raise BackendError("Unsupported arguments")
            args = [args[1], args[0]]

        return f(*args)

    return normalizer


class BackendVSA(Backend):
    def __init__(self):
        Backend.__init__(self)
        self._make_expr_ops(set(expression_set_operations), op_class=self)
        self._make_raw_ops(set(backend_operations_vsa_compliant), op_module=BackendVSA)

        self._op_raw["Reverse"] = BackendVSA.Reverse
        self._op_raw["If"] = self.If
        self._op_expr["BVV"] = self.BVV
        self._op_expr["BoolV"] = self.BoolV
        self._op_expr["BVS"] = self.BVS

        # reduceable
        self._op_raw["__add__"] = self._op_add
        self._op_raw["__sub__"] = self._op_sub
        self._op_raw["__mul__"] = self._op_mul
        self._op_raw["__or__"] = self._op_or
        self._op_raw["__xor__"] = self._op_xor
        self._op_raw["__and__"] = self._op_and
        self._op_raw["__mod__"] = self._op_mod

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

    @staticmethod
    def _op_mod(*args):
        return reduce(operator.__mod__, args)

    def convert(self, expr):
        return Backend.convert(self, expr.ite_excavated if isinstance(expr, Base) else expr)

    def _convert(self, a):
        if isinstance(a, numbers.Number):
            return a
        if isinstance(a, bool):
            return TrueResult() if a else FalseResult()
        if isinstance(a, StridedInterval | DiscreteStridedIntervalSet | ValueSet):
            return a
        if isinstance(a, BoolResult):
            return a

        # Not supported
        raise BackendError

    def _eval(self, expr, n, extra_constraints=(), solver=None, model_callback=None):
        if isinstance(expr, StridedInterval | ValueSet):
            return expr.eval(n)
        if isinstance(expr, BoolResult):
            return expr.value
        raise BackendError(f"Unsupported type {type(expr)}")

    def _min(self, expr, extra_constraints=(), signed=False, solver=None, model_callback=None):
        # TODO: signed min
        if isinstance(expr, StridedInterval):
            if expr.is_top:
                # TODO: Return
                return 0

            return expr.min

        if isinstance(expr, ValueSet):
            return expr.min

        raise BackendError(f"Unsupported expr type {type(expr)}")

    def _max(self, expr, extra_constraints=(), signed=False, solver=None, model_callback=None):
        # TODO: signed max
        if isinstance(expr, StridedInterval):
            if expr.is_top:
                # TODO:
                return StridedInterval.max_int(expr.bits)

            return expr.max

        if isinstance(expr, ValueSet):
            return expr.max

        raise BackendError(f"Unsupported expr type {type(expr)}")

    def _solution(self, obj, v, extra_constraints=(), solver=None, model_callback=None):
        if isinstance(obj, BoolResult):
            return len(set(v.value) & set(obj.value)) > 0

        if isinstance(obj, StridedInterval):
            return not obj.intersection(v).is_empty

        if isinstance(obj, ValueSet):
            return any(not si.intersection(v).is_empty for _, si in obj.items())

        raise NotImplementedError(type(obj).__name__)

    def _has_true(self, o, extra_constraints=(), solver=None, model_callback=None):
        return BoolResult.has_true(o)

    def _has_false(self, o, extra_constraints=(), solver=None, model_callback=None):
        return BoolResult.has_false(o)

    def _is_true(self, o, extra_constraints=(), solver=None, model_callback=None):
        return BoolResult.is_true(o)

    def _is_false(self, o, extra_constraints=(), solver=None, model_callback=None):
        return BoolResult.is_false(o)

    #
    # Backend Operations
    #

    def simplify(self, e):
        raise BackendError("nope")

    def _identical(self, a, b):
        if type(a) != type(b):  # noqa: E721
            return False
        return a.identical(b)

    def _unique(self, obj):
        if isinstance(obj, StridedInterval | ValueSet):
            return obj.unique
        raise BackendError(f"Not supported type of operand {type(obj)}")

    @staticmethod
    def _cardinality(a):
        return a.cardinality

    def name(self, a):
        if isinstance(a, StridedInterval):
            return a.name

        return None

    def apply_annotation(self, bo, annotation):
        """
        Apply an annotation on the backend object.

        :param BackendObject bo: The backend object.
        :param Annotation annotation: The annotation to be applied
        :return: A new BackendObject
        :rtype: BackendObject
        """

        # Currently we only support RegionAnnotation

        if not isinstance(annotation, RegionAnnotation):
            return bo

        if not isinstance(bo, ValueSet):
            # Convert it to a ValueSet first
            # Note that the original value is not kept at all. If you want to convert a StridedInterval to a ValueSet,
            # you gotta do the conversion by calling AST.annotate() from outside.
            bo = ValueSet.empty(bo.bits)

        return bo.apply_annotation(annotation)

    def BVV(self, ast):
        if ast.args[0] is None:
            return StridedInterval.empty(ast.args[1])
        return CreateStridedInterval(bits=ast.args[1], stride=0, lower_bound=ast.args[0], upper_bound=ast.args[0])

    @staticmethod
    def BoolV(ast):
        return TrueResult() if ast.args[0] else FalseResult()

    @staticmethod
    def And(a, *args):
        return reduce(operator.__and__, args, a)

    @staticmethod
    def Not(a):
        return ~a

    @staticmethod
    @normalize_arg_order
    def ULT(a, b):
        return a.ULT(b)

    @staticmethod
    @normalize_arg_order
    def ULE(a, b):
        return a.ULE(b)

    @staticmethod
    @normalize_arg_order
    def UGT(a, b):
        return a.UGT(b)

    @staticmethod
    @normalize_arg_order
    def UGE(a, b):
        return a.UGE(b)

    @staticmethod
    @normalize_arg_order
    def SLT(a, b):
        return a.SLT(b)

    @staticmethod
    @normalize_arg_order
    def SLE(a, b):
        return a.SLE(b)

    @staticmethod
    @normalize_arg_order
    def SGT(a, b):
        return a.SGT(b)

    @staticmethod
    @normalize_arg_order
    def SGE(a, b):
        return a.SGE(b)

    @staticmethod
    def BVS(ast):
        size = ast.size()
        name, mn, mx, stride, uninitialized, discrete_set, max_card = ast.args
        return CreateStridedInterval(
            name=name,
            bits=size,
            lower_bound=mn,
            upper_bound=mx,
            stride=stride,
            uninitialized=uninitialized,
            discrete_set=discrete_set,
            discrete_set_max_cardinality=max_card,
        )

    def If(self, cond, t, f):
        if not self.has_true(cond):
            return f
        if not self.has_false(cond):
            return t
        return t.union(f)

    # TODO: Implement other operations!

    @staticmethod
    def Or(*args):
        first = args[0]
        others = args[1:]

        for o in others:
            first = first.union(o)
        return first

    @staticmethod
    def __rshift__(expr, shift_amount):  # pylint:disable=unexpected-special-method-signature
        return expr.__rshift__(shift_amount)

    @staticmethod
    def LShR(expr, shift_amount):
        return expr.LShR(shift_amount)

    @staticmethod
    def Concat(*args):
        ret = None
        for expr in args:
            if not isinstance(expr, StridedInterval | DiscreteStridedIntervalSet | ValueSet):
                raise BackendError(f"Unsupported expr type {type(expr)}")

            ret = ret.concat(expr) if ret is not None else expr

        return ret

    @staticmethod
    def Extract(*args):
        low_bit = args[1]
        high_bit = args[0]
        expr = args[2]

        if not isinstance(expr, StridedInterval | DiscreteStridedIntervalSet | ValueSet):
            raise BackendError(f"Unsupported expr type {type(expr)}")

        return expr.extract(high_bit, low_bit)

    @staticmethod
    def SignExt(*args):
        new_bits = args[0]
        expr = args[1]

        if not isinstance(expr, StridedInterval | DiscreteStridedIntervalSet):
            raise BackendError(f"Unsupported expr type {type(expr)}")

        return expr.sign_extend(new_bits + expr.bits)

    @staticmethod
    def ZeroExt(*args):
        new_bits = args[0]
        expr = args[1]

        if not isinstance(expr, StridedInterval | DiscreteStridedIntervalSet):
            raise BackendError(f"Unsupported expr type {type(expr)}")

        return expr.zero_extend(new_bits + expr.bits)

    @staticmethod
    def Reverse(arg):
        if not isinstance(arg, StridedInterval | DiscreteStridedIntervalSet | ValueSet):
            raise BackendError(f"Unsupported expr type {type(arg)}")

        return arg.reverse()

    def union(self, ast):
        if len(ast.args) != 2:
            raise BackendError("Incorrect number of arguments (%d) passed to BackendVSA.union()." % len(ast.args))

        converted_0 = self.convert(ast.args[0])
        converted_1 = self.convert(ast.args[1])

        ret = converted_0.union(converted_1)

        if ret is NotImplemented:
            l.debug("Union failed, trying the other way around.")
            ret = converted_1.union(converted_0)

        return ret

    def intersection(self, ast):
        if len(ast.args) != 2:
            raise BackendError(
                "Incorrect number of arguments (%d) passed to BackendVSA.intersection()." % len(ast.args)
            )

        ret = None

        for arg in ast.args:
            arg = self.convert(arg)
            ret = arg if ret is None else ret.intersection(arg)
        return ret

    def widen(self, ast):
        if len(ast.args) != 2:
            raise BackendError("Incorrect number of arguments (%d) passed to BackendVSA.widen()." % len(ast.args))

        converted_0 = self.convert(ast.args[0])
        converted_1 = self.convert(ast.args[1])

        ret = converted_0.widen(converted_1)
        if ret is NotImplemented:
            l.debug("Widening failed, trying the other way around.")
            ret = converted_1.widen(converted_0)

        return ret

    @staticmethod
    def CreateTopStridedInterval(bits, name=None, uninitialized=False):
        return StridedInterval.top(bits, name, uninitialized=uninitialized)

    def constraint_to_si(self, expr):
        return Balancer(self, expr).compat_ret


BackendVSA.CreateStridedInterval = staticmethod(CreateStridedInterval)
