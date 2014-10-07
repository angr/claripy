import logging
l = logging.getLogger("claripy.backends.backend_vsa")

from .model_backend import ModelBackend, BackendError

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

    def add_exprs(self, solver, constraints):
        pass

    def results_exprs(self, solver, extra_constraints, generic_backend):
        return Result(True, self)

    def convert(self, a, result=None):
        if type(a) in { int, long, float, bool, str, BVV }:
            return a
        if type(a) in { StridedInterval, ValueSet }:
            return a

        import ipdb; ipdb.set_trace()
        raise NotImplementedError()

    def eval(self, expr, n, result=None):
        assert type(expr) == StridedInterval

        results = []
        lb = expr.lower_bound

        while len(results) < n and lb <= expr.upper_bound:
            results.append(lb)
            lb += expr.stride

        return results

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


    #
    # Operations
    #

    @staticmethod
    def __add__(a, b): return a.__add__(b)

    @staticmethod
    def __sub__(a, b): return a.__sub__(b)

    @staticmethod
    def __and__(a, b): return a.__and__(b)

    # TODO: Implement other operations!

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
    def size(arg):
        return len(arg)

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
from ..vsa import StridedInterval, ValueSet, AbstractLocation
from ..result import Result