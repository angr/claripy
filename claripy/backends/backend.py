import logging
l = logging.getLogger('claripy.backends.backend')

class Backend(object):
    def __init__(self):
        self._op_raw = { }
        self._op_raw_result = { } # these are operations that work on raw objects and accept a result arg
        self._op_expr = { }
        self._cache_objects = True
        self._claripy = None

    def set_claripy_object(self, claripy):
        self._claripy = claripy

    def _make_raw_ops(self, op_list, op_dict=None, op_module=None):
        for o in op_list:
            if op_dict is not None:
                if o in op_dict:
                    self._op_raw[o] = op_dict[o]
                else:
                    l.warning("Operation %s not in op_dict.", o)
            else:
                if hasattr(op_module, o):
                    self._op_raw[o] = getattr(op_module, o)
                else:
                    l.warning("Operation %s not in op_module %s.", o, op_module)

    def _make_expr_ops(self, op_list, op_dict=None, op_class=None):
        '''
        Fill up self._op_expr dict
        :param op_list: A list of operation names
        :param op_dict: A dictionary of operation methods
        :param op_class: Where the operation method comes from
        :return:
        '''
        for o in op_list:
            if op_dict is not None:
                if o in op_dict:
                    self._op_expr[o] = op_dict[o]
                else:
                    l.warning("Operation %s not in op_dict.", o)
            else:
                if hasattr(op_class, o):
                    self._op_expr[o] = getattr(op_class, o)
                else:
                    l.warning("Operation %s not in op_class %s.", o, op_class)

    #
    # These functions handle converting expressions to formats that the backend
    # can understand.
    #

    def _convert(self, r, result=None): #pylint:disable=W0613,R0201
        '''
        Converts r to something usable by this backend.
        '''
        return r

    def convert(self, expr, result=None): #pylint:disable=R0201
        '''
        Resolves a claripy.E into something usable by the backend.

        @param expr: the expression
        @param save: save the result in the expression's object cache
        @param result: a Result object (for concrete-only symbolic evaluation)
        @returns a backend object
        '''
        if isinstance(expr, A):
            #l.debug('converting A')
            return expr.resolve_backend(self, result=result)
        elif not isinstance(expr, E):
            #l.debug('converting non-expr')
            return self._convert(expr, result=result)
        else:
            #l.debug('converting expr')
            return expr.model_for(self, result=result)

    def convert_list(self, args, result=None):
        return [ self.convert(a, result=result) for a in args ]

    #
    # These functions provide support for applying operations to expressions.
    #

    def call(self, ast, result=None):
        '''
        Calls the operation specified in the AST on the nodes of the AST.

        @returns an Expression with the result.
        '''
        if ast.op in self._op_expr:
            return self._op_expr[ast.op](*ast.args, result=result)
        else:
            converted = self.convert_list(ast.args, result=result)

            if ast.op in self._op_raw_result:
                obj = self._op_raw_result[ast.op](*converted, result=result)
            elif ast.op in self._op_raw:
                # the raw ops don't get the model, cause, for example, Z3 stuff can't take it
                obj = self._op_raw[ast.op](*converted)
            elif not ast.op.startswith("__"):
                l.debug("backend has no operation %s", ast.op)
                raise BackendError("backend has no operation %s" % ast.op)
            else:
                obj = NotImplemented

                # first, try the operation with the first guy
                if hasattr(converted[0], ast.op):
                    op = getattr(converted[0], ast.op)
                    obj = op(*converted[1:])
                # now try the reverse operation with the second guy
                if obj is NotImplemented and len(converted) == 2 and hasattr(converted[1], opposites[ast.op]):
                    op = getattr(converted[1], opposites[ast.op])
                    obj = op(converted[0])

                if obj is NotImplemented:
                    l.debug("%s neither %s nor %s apply in backend.call()", self, ast.op, opposites[ast.op])
                    raise BackendError("unable to apply operation on provided converted")

            return obj

    #
    # Abstraction and resolution.
    #

    def abstract(self, e, split_on=None): #pylint:disable=W0613,R0201
        raise BackendError("backend %s doesn't implement abstract()" % self.__class__.__name__)

    #
    # These functions simplify expressions.
    #

    def simplify_expr(self, e):
        o = self.simplify(self.convert(e))
        # TODO: keep UUID
        return E(self._claripy, self.abstract(o), e.variables, e.symbolic, objects={self: o})

    def simplify(self, e): # pylint:disable=R0201,unused-argument
        raise BackendError("backend %s can't simplify" % self.__class__.__name__)

from ..expression import E
from ..ast import A
from ..operations import opposites
from ..errors import BackendError
