import operator

from .backend import Backend
from .backend import ops as func_ops
from ..expression import operations as attr_ops

class BackendAbstract(Backend):
    def __init__(self, claripy):
        Backend.__init__(self, claripy)

        for o in func_ops | attr_ops:
            self._op_expr[o] = self._make_abstract_op(o)
        self._op_expr['BitVec'] = self.BitVec

    def BitVec(self, name, size, model=None): #pylint:disable=W0613
        return E(self._claripy, variables={name}, symbolic=True, ast=A('BitVec', (name, size)))

    def _make_abstract_op(self, name):
        def op(*args, **kwargs): #pylint:disable=W0613
            variables = reduce(operator.or_, (a.variables for a in args if isinstance(a, E)), set())
            symbolic = any((a.symbolic for a in args if isinstance(a, E)))
            return E(self._claripy, variables=variables, symbolic=symbolic, ast=A(name, args))
        op.__name__ = name
        return op

from ..expression import E, A
