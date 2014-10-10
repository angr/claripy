import logging
import functools

l = logging.getLogger("claripy.backends.backend_vsa")

from .model_backend import ModelBackend, BackendError

def arg_filter(f):
    @functools.wraps(f)
    def filter(*args):
        if type(args[0]) in {int, long}:
            raise BackendError('Unsupported argument type %s' % type(args[0]))
        return f(*args)

    return filter

def normalize_arg_order(f):
    @functools.wraps(f)
    def normalizer(*args):
        if len(args) != 2:
            raise BackendError('Unsupported arguments number %d' % len(args))

        if type(args[0]) not in { StridedInterval, ValueSet }:
            if type(args[1]) not in { StridedInterval, ValueSet }:
                raise BackendError('Unsupported arguments')
            args = [args[1], args[0]]

        return f(*args)

    return normalizer

def normalize_boolean_arg_types(f):
    def convert_bool(a):
        if isinstance(a, BoolResult):
            return a
        if a == True:
            return TrueResult()
        elif a == False:
            return FalseResult()
        else:
            raise BackendError('Unsupported type %s' % type(a))

    @functools.wraps(f)
    def normalizer(*args):
        new_args = [convert_bool(a) for a in args]

        return f(*new_args)

    return normalizer

class BackendVSA(ModelBackend):
    def __init__(self):
        ModelBackend.__init__(self)
        self._make_raw_ops(set(expression_operations), op_module=BackendVSA)
        self._make_raw_ops(set(backend_operations_vsa_compliant), op_module=BackendVSA)

        self._op_raw['StridedInterval'] = BackendVSA.CreateStridedInterval
        self._op_raw['ValueSet'] = ValueSet.__init__
        self._op_raw['AbstractLocation'] = AbstractLocation.__init__
        self._op_raw['size'] = BackendVSA.size
        self._op_raw['Reverse'] = BackendVSA.Reverse
        self._op_raw['If'] = BackendVSA.If

    def add_exprs(self, solver, constraints):
        pass

    def results_exprs(self, solver, extra_constraints, generic_backend):
        return Result(True, self)

    def convert(self, a, result=None):
        if type(a) in { int, long, float, bool, str, BVV }:
            return a
        if type(a) in { StridedInterval, ValueSet }:
            return a
        if isinstance(a, BoolResult):
            return a

        import ipdb; ipdb.set_trace()
        raise NotImplementedError()

    def eval(self, expr, n, result=None):
        if isinstance(expr, StridedInterval):
            results = []
            lb = expr.lower_bound

            while len(results) < n and lb <= expr.upper_bound:
                results.append(lb)
                lb += expr.stride

            return results
        elif isinstance(expr, BoolResult):
            return expr.value
        else:
            raise BackendError('Unsupported type %s' % type(expr))

    def min(self, expr, result=None):
        assert type(expr) == StridedInterval

        if expr.is_top():
            # TODO: Return
            return StridedInterval.min_int(expr.bits)

        return expr.lower_bound

    def max(self, expr, result=None):
        assert type(expr) == StridedInterval

        if expr.is_top():
            # TODO:
            return StridedInterval.max_int(expr.bits)

        return expr.upper_bound

    def has_true(self, o):
        return o == True or (isinstance(o, BoolResult) and True in o.value)

    def has_false(self, o):
        return o == False or (isinstance(o, BoolResult) and False in o.value)

    def is_true(self, o):
        return o == True or (isinstance(o, TrueResult))

    def is_false(self, o):
        return o == False or (isinstance(o, FalseResult))
    #
    # Operations
    #

    @staticmethod
    @normalize_arg_order
    def __add__(a, b): return a.__add__(b)

    @staticmethod
    @normalize_arg_order
    def __sub__(a, b): return a.__sub__(b)

    @staticmethod
    @normalize_arg_order
    def __and__(a, b): return a.__and__(b)

    @staticmethod
    @normalize_arg_order
    def __rand__(a, b): return a.__and__(b)

    @staticmethod
    @normalize_arg_order
    def __eq__(a, b): return a.__eq__(b)

    @staticmethod
    @normalize_arg_order
    def __ne__(a, b): return a.__ne__(b)

    @staticmethod
    @normalize_arg_order
    def __or__(a, b): return a.__or__(b)

    @staticmethod
    @normalize_arg_order
    def __xor__(a, b): return a.__xor__(b)

    @staticmethod
    @normalize_arg_order
    def __rxor__(a, b): return a.__xor__(b)

    @staticmethod
    def __lshift__(a, b): return a.__lshift__(b)

    @staticmethod
    @normalize_boolean_arg_types
    def And(a, b):
        return a & b

    @staticmethod
    @normalize_boolean_arg_types
    def Not(a):
        return ~a

    @staticmethod
    @normalize_arg_order
    def ULT(a, b):
        return a < b

    @staticmethod
    def If(cond, true_expr, false_expr):
        exprs = []
        if True in cond.value:
            exprs.append(true_expr)
        if False in cond.value:
            exprs.append(false_expr)

        if len(exprs) == 1:
            expr = exprs[0]
        else:
            # TODO: How to handle it?
            expr = Or(exprs[0], exprs[1])

        return expr

    # TODO: Implement other operations!

    @staticmethod
    def LShR(expr, shift_amount):
        return expr >> shift_amount

    @staticmethod
    def Reverse(arg):
        print 'Reversing %s' % arg
        return arg.reverse()

    @staticmethod
    def Concat(*args):
        ret = None
        for expr in args:
            assert type(expr) in { StridedInterval, ValueSet, BVV }
            if type(expr) is BVV:
                expr = BackendVSA.CreateStridedInterval(bits=expr.bits, to_conv=expr)

            ret = ret.concat(expr) if ret is not None else expr

        return ret

    @staticmethod
    @arg_filter
    def size(arg):
        if type(arg) in { StridedInterval, ValueSet }:
            return len(arg)
        else:
            return arg.size()

    @staticmethod
    def Extract(*args):
        low_bit = args[1]
        high_bit = args[0]
        expr = args[2]

        assert type(expr) in { StridedInterval, ValueSet }

        ret = expr.extract(high_bit, low_bit)

        return ret

    @staticmethod
    def ZeroExt(*args):
        new_bits = args[0]
        expr = args[1]

        assert type(expr) is StridedInterval
        return expr.zero_extend(new_bits + expr.bits)

    @staticmethod
    def Reverse(arg):
        assert type(arg) in { StridedInterval, ValueSet }

        return arg.reverse()

    @staticmethod
    def union(*args):
        assert len(args) == 2

        return args[0].union(args[1])

    @staticmethod
    def CreateStridedInterval(name=None, bits=0, stride=None, lower_bound=None, upper_bound=None, to_conv=None):
        '''

        :param name:
        :param bits:
        :param stride:
        :param lower_bound:
        :param upper_bound:
        :param to_conv:
        :return:
        '''
        if to_conv is not None:
            if type(to_conv) is E:
                to_conv = to_conv._model
            if type(to_conv) is StridedInterval:
                # No conversion will be done
                return to_conv

            if type(to_conv) not in {int, long, BVV}:
                raise BackendError('Unsupported to_conv type %s' % type(to_conv))

            if stride is not None or lower_bound is not None or \
                            upper_bound is not None:
                raise BackendError('You cannot specify both to_conv and other parameters at the same time.')

            if type(to_conv) is BVV:
                bits = to_conv.bits
                to_conv_value = to_conv.value
            else:
                bits = bits
                to_conv_value = to_conv

            stride = 0
            lower_bound = to_conv_value
            upper_bound = to_conv_value

        bi = StridedInterval(name=name,
                             bits=bits,
                             stride=stride,
                             lower_bound=lower_bound,
                             upper_bound=upper_bound)
        return bi

from ..bv import BVV
from ..expression import E
from ..operations import backend_operations_vsa_compliant, backend_vsa_creation_operations, expression_operations
from ..vsa import StridedInterval, ValueSet, AbstractLocation, BoolResult, TrueResult, FalseResult
from ..result import Result