from .backend import Backend
from .backend import ops as func_ops
from ..expressions.expression import ops as attr_ops

class BackendAbstract(Backend):
    def _make_abstract_op(self, name):
        def op(*args):
            backends = [ self ]
            for a in args:
                if isinstance(a, Expression):
                    backends = a._backends
                    break

            variables, symbolic, _ = self.combined_info(args)
            return Expression(backends, variables=variables, symbolic=symbolic, obj=AbstractCall(name, args))
        op.__name__ = name
        return op

    def __init__(self):
        Backend.__init__(self)

        for o in func_ops | attr_ops:
            self._op_expr[o] = self._make_abstract_op(o)

from .abstract_call import AbstractCall
from ..expressions.expression import Expression
