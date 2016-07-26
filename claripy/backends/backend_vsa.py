import logging
import functools
import operator

l = logging.getLogger("claripy.backends.backend_vsa")

from . import Backend, BackendError
from ..vsa import RegionAnnotation

def arg_filter(f):
    @functools.wraps(f)
    def filter(*args): #pylint:disable=redefined-builtin
        if type(args[0]) in {int, long}: #pylint:disable=unidiomatic-typecheck
            raise BackendError('Unsupported argument type %s' % type(args[0]))
        return f(*args)

    return filter

def normalize_arg_order(f):
    @functools.wraps(f)
    def normalizer(*args):
        if len(args) != 2:
            raise BackendError('Unsupported arguments number %d' % len(args))

        if type(args[0]) not in { StridedInterval, DiscreteStridedIntervalSet, ValueSet }: #pylint:disable=unidiomatic-typecheck
            if type(args[1]) not in { StridedInterval, DiscreteStridedIntervalSet, ValueSet }: #pylint:disable=unidiomatic-typecheck
                raise BackendError('Unsupported arguments')
            args = [args[1], args[0]]

        return f(*args)

    return normalizer

def convert_args(f):
    @functools.wraps(f)
    def converter(self, ast):
        raw_args = []
        for i in xrange(len(ast.args)):
            # It's not reversed
            raw_args.append(ast.args[i])

        for i in xrange(len(raw_args)):
            raw_args[i] = self.convert(raw_args[i])

        normalized = ast.swap_args(raw_args)
        ret = f(self, normalized)

        return ret

    return converter

class BackendVSA(Backend):
    def __init__(self):
        Backend.__init__(self)
        # self._make_raw_ops(set(expression_operations) - set(expression_set_operations), op_module=BackendVSA)
        self._make_expr_ops(set(expression_set_operations), op_class=self)
        self._make_raw_ops(set(backend_operations_vsa_compliant), op_module=BackendVSA)

        self._op_raw['StridedInterval'] = BackendVSA.CreateStridedInterval
        self._op_raw['ValueSet'] = ValueSet.__init__
        self._op_raw['AbstractLocation'] = AbstractLocation.__init__
        self._op_raw['Reverse'] = BackendVSA.Reverse
        self._op_raw['If'] = self.If
        self._op_expr['BVV'] = self.BVV
        self._op_expr['BoolV'] = self.BoolV
        self._op_expr['BVS'] = self.BVS

        # reduceable
        self._op_raw['__add__'] = self._op_add
        self._op_raw['__sub__'] = self._op_sub
        self._op_raw['__mul__'] = self._op_mul
        self._op_raw['__or__'] = self._op_or
        self._op_raw['__xor__'] = self._op_xor
        self._op_raw['__and__'] = self._op_and

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

    def convert(self, expr):
        return Backend.convert(self, expr.ite_excavated if isinstance(expr, Base) else expr)

    def _convert(self, a):
        if type(a) in { int, long }: #pylint:disable=unidiomatic-typecheck
            return a
        if type(a) is bool:
            return TrueResult() if a else FalseResult()
        if type(a) in { StridedInterval, DiscreteStridedIntervalSet, ValueSet }: #pylint:disable=unidiomatic-typecheck
            return a
        if isinstance(a, BoolResult):
            return a

        # Not supported
        raise BackendError()

    def _eval(self, expr, n, extra_constraints=(), solver=None, model_callback=None):
        if isinstance(expr, StridedInterval):
            return expr.eval(n)
        elif isinstance(expr, ValueSet):
            results = []

            while len(results) < n:
                results.extend(expr.eval(n - len(results)))

            return results
        elif isinstance(expr, BoolResult):
            return expr.value
        else:
            raise BackendError('Unsupported type %s' % type(expr))

    def _min(self, expr, extra_constraints=(), solver=None, model_callback=None):
        if isinstance(expr, StridedInterval):
            if expr.is_top:
                # TODO: Return
                return 0

            return expr.min
        else:
            raise BackendError('Unsupported expr type %s' % type(expr))

    def _max(self, expr, extra_constraints=(), solver=None, model_callback=None):
        if isinstance(expr, StridedInterval):
            if expr.is_top:
                # TODO:
                return StridedInterval.max_int(expr.bits)

            return expr.max

        else:
            raise BackendError('Unsupported expr type %s' % type(expr))

    def _solution(self, obj, v, extra_constraints=(), solver=None, model_callback=None):
        if isinstance(obj, BoolResult):
            return len(set(v.value) & set(obj.value)) > 0

        if isinstance(obj, StridedInterval):
            return not obj.intersection(v).is_empty

        if isinstance(obj, ValueSet):
            for _, si in obj.items():
                if not si.intersection(v).is_empty:
                    return True
            return False

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
        raise BackendError('nope')

    def _identical(self, a, b):
        if type(a) != type(b):
            return False
        return a.identical(b)

    def _unique(self, obj): #pylint:disable=unused-argument,no-self-use
        if isinstance(obj, StridedInterval):
            return obj.unique
        elif isinstance(obj, ValueSet):
            return obj.unique
        else:
            raise BackendError('Not supported type of operand %s' % type(obj))

    def _cardinality(self, a): #pylint:disable=unused-argument,no-self-use
        return a.cardinality

    def name(self, a):
        if isinstance(a, StridedInterval):
            return a.name

        else:
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

    def BVV(self, ast): #pylint:disable=unused-argument,no-self-use
        if ast.args[0] is None:
            return StridedInterval.empty(ast.args[1])
        else:
            return CreateStridedInterval(bits=ast.args[1], stride=0, lower_bound=ast.args[0], upper_bound=ast.args[0])

    @staticmethod
    def BoolV(ast): #pylint:disable=unused-argument
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
    def BVS(ast): #pylint:disable=unused-argument
        size = ast.size()
        name, mn, mx, stride, uninitialized, discrete_set, max_card = ast.args
        return CreateStridedInterval(name=name, bits=size, lower_bound=mn, upper_bound=mx, stride=stride,
                                     uninitialized=uninitialized, discrete_set=discrete_set,
                                     discrete_set_max_cardinality=max_card)

    def If(self, cond, t, f):
        if not self.has_true(cond):
            return f
        elif not self.has_false(cond):
            return t
        else:
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
    def __rshift__(expr, shift_amount): #pylint:disable=unexpected-special-method-signature
        return expr.__rshift__(shift_amount)

    @staticmethod
    def LShR(expr, shift_amount):
        return expr.LShR(shift_amount)

    @staticmethod
    def Concat(*args):
        ret = None
        for expr in args:
            if type(expr) not in { StridedInterval, DiscreteStridedIntervalSet, ValueSet }: #pylint:disable=unidiomatic-typecheck
                raise BackendError('Unsupported expr type %s' % type(expr))

            ret = ret.concat(expr) if ret is not None else expr

        return ret

    @arg_filter
    def _size(self, arg):
        if type(arg) in { StridedInterval, DiscreteStridedIntervalSet, ValueSet }: #pylint:disable=unidiomatic-typecheck
            return len(arg)
        else:
            return arg.size()

    @staticmethod
    def Extract(*args):
        low_bit = args[1]
        high_bit = args[0]
        expr = args[2]

        if type(expr) not in { StridedInterval, DiscreteStridedIntervalSet, ValueSet }: #pylint:disable=unidiomatic-typecheck
            raise BackendError('Unsupported expr type %s' % type(expr))

        ret = expr.extract(high_bit, low_bit)

        return ret

    @staticmethod
    def SignExt(*args):
        new_bits = args[0]
        expr = args[1]

        if type(expr) not in { StridedInterval, DiscreteStridedIntervalSet }: #pylint:disable=unidiomatic-typecheck
            raise BackendError('Unsupported expr type %s' % type(expr))

        return expr.sign_extend(new_bits + expr.bits)

    @staticmethod
    def ZeroExt(*args):
        new_bits = args[0]
        expr = args[1]

        if type(expr) not in { StridedInterval, DiscreteStridedIntervalSet }: #pylint:disable=unidiomatic-typecheck
            raise BackendError('Unsupported expr type %s' % type(expr))

        return expr.zero_extend(new_bits + expr.bits)

    @staticmethod
    def Reverse(arg):
        if type(arg) not in {StridedInterval, DiscreteStridedIntervalSet, ValueSet}: #pylint:disable=unidiomatic-typecheck
            raise BackendError('Unsupported expr type %s' % type(arg))

        return arg.reverse()

    @convert_args
    def union(self, ast): #pylint:disable=unused-argument,no-self-use
        if len(ast.args) != 2:
            raise BackendError('Incorrect number of arguments (%d) passed to BackendVSA.union().' % len(ast.args))

        ret = ast.args[0].union(ast.args[1])

        if ret is NotImplemented:
            ret = ast.args[1].union(ast.args[0])

        return ret

    @convert_args
    def intersection(self, ast): #pylint:disable=unused-argument,no-self-use
        if len(ast.args) != 2:
            raise BackendError('Incorrect number of arguments (%d) passed to BackendVSA.intersection().' % len(ast.args))

        ret = None

        for arg in ast.args:
            if ret is None:
                ret = arg
            else:
                ret = ret.intersection(arg)
        return ret

    @convert_args
    def widen(self, ast): #pylint:disable=unused-argument,no-self-use
        if len(ast.args) != 2:
            raise BackendError('Incorrect number of arguments (%d) passed to BackendVSA.widen().' % len(ast.args))

        ret = ast.args[0].widen(ast.args[1])
        if ret is NotImplemented:
            ret = ast.args[1].widen(ast.args[0])

        return ret

    @staticmethod
    def CreateTopStridedInterval(bits, name=None, uninitialized=False): #pylint:disable=unused-argument,no-self-use
        return StridedInterval.top(bits, name, uninitialized=uninitialized)

    def constraint_to_si(self, expr):
        return Balancer(self, expr).compat_ret

from ..ast.base import Base
from ..operations import backend_operations_vsa_compliant, expression_set_operations
from ..vsa import StridedInterval, CreateStridedInterval, DiscreteStridedIntervalSet, ValueSet, AbstractLocation, BoolResult, TrueResult, FalseResult
from ..balancer import Balancer

BackendVSA.CreateStridedInterval = staticmethod(CreateStridedInterval)
