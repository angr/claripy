import sys
import ctypes
import weakref

import logging
l = logging.getLogger('claripy.backend')

class BackendObject(object):
    '''
    This is a base class for custom backend objects to implement.

    It lets Claripy know that how to deal with those objects, in case they're
    directly used in operations.

    Backend objects that *don't* derive from this class need to be wrapped in
    a type-I claripy.ast.Base.
    '''

    def to_claripy(self):
        '''
        Claripy calls this to retrieve something that it can directly reason
        about.
        '''

        return self

class Backend(object):
    '''
    Backends are Claripy's workhorses. Claripy exposes ASTs (claripy.ast.Base objects)
    to the world, but when actual computation has to be done, it pushes those
    ASTs into objects that can be handled by the backends themselves. This
    provides a unified interface to the outside world while allowing Claripy to
    support different types of computation. For example, BackendConcrete
    provides computation support for concrete bitvectors and booleans,
    BackendVSA introduces VSA constructs such as StridedIntervals (and details
    what happens when operations are performed on them), and BackendZ3 provides
    support for symbolic variables and constraint solving.

    There are a set of functions that a backend is expected to implement. For
    all of these functions, the "public" version is expected to be able to deal
    with claripy.ast.Base objects, while the "private" version should only deal with
    objects specific to the backend itself. This is distinguished with Python
    idioms: a public function will be named func() while a private function
    will be _func(). All functions should return objects that are usable by the
    backend in its private methods. If this can't be done (i.e., some
    functionality is being attempted that the backend can't handle), the
    backend should raise a BackendError. In this case, Claripy will move on to
    the next backend in its list.

    All backends must implement a convert() function. This function receives a
    claripy.A and should return an object that the backend can handle in its
    private methods. Backends should also implement a _convert() method, which
    will receive anything that is *not* a claripy.A object (i.e., an integer or
    an object from a different backend). If convert() or _convert() receives
    something that the backend can't translate to a format that is usable
    internally, the backend should raise BackendError, and thus won't be used
    for that object.

    Claripy contract with its backends is as follows: backends should be able
    to can handle, in their private functions, any object that they return from
    their private *or* public functions. Likewise, Claripy will never pass an
    object to any backend private function that did not originate as a return
    value from a private or public function of that backend. One exception to
    this is _convert(), as Claripy can try to stuff anything it feels like into
    _convert() to see if the backend can handle that type of object.
    '''


    def __init__(self):
        self._op_raw = { }
        self._op_raw_result = { } # these are operations that work on raw objects and accept a result arg
        self._op_expr = { }
        self._cache_objects = True
        self._object_cache = weakref.WeakKeyDictionary()
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
                    l.debug("Operation %s not in op_module %s.", o, op_module)
        self._op_raw['I'] = lambda thing: thing

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
        Resolves a claripy.Base into something usable by the backend.

        @param expr: the expression
        @param save: save the result in the expression's object cache
        @param result: a Result object (for concrete-only symbolic evaluation)
        @returns a backend object
        '''
        if isinstance(expr, Base):
            r = None
            # if we have a result, and it's cached there, use it
            if result is not None:
                try: return result.resolve_cache[self][expr._cache_key]
                except KeyError: pass

            # otherwise, if it's cached in the backend, use it
            if r is None:
                try: return self._object_cache[expr._cache_key]
                except KeyError: pass

            #l.debug('converting A')

            # otherwise, try to convert something
            if r is None and result is not None:
                for rc in result.resolve_cache.values():
                    try:
                        r = self._convert(rc[expr._cache_key], result=result)
                    except (KeyError, BackendError):
                        pass
            if r is None:
                for b in self._claripy.model_backends + self._claripy.solver_backends:
                    try:
                        r = self._convert(b._object_cache[expr._cache_key])
                    except (KeyError, BackendError):
                        pass

            # otherwise, resolve it!
            r = expr.resolved_with(self, result=result)

            if result is None: self._object_cache[expr._cache_key] = r
            else: result.resolve_cache[self][expr._cache_key] = r
            return r
        else:
            #l.debug('converting non-expr')
            return self._convert(expr, result=result)

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

        if result is None:
            try: return self._object_cache[ast._cache_key]
            except KeyError: pass
        else:
            try: return result.resolve_cache[self][ast._cache_key]
            except KeyError: pass

        try:
            if ast.op in self._op_expr:
                r = self._op_expr[ast.op](*ast.args, result=result)
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

                r = obj
        except (RuntimeError, ctypes.ArgumentError):
            e_type, value, traceback = sys.exc_info()
            raise ClaripyRecursionError, ("Recursion limit reached. I sorry.", e_type, value), traceback

        if result is None: self._object_cache[ast._cache_key] = r
        else: result.resolve_cache[self][ast._cache_key] = r
        return r

    #
    # Abstraction and resolution.
    #

    def abstract(self, e): #pylint:disable=W0613,R0201
        '''
        Abstracts the BackendObject e to an AST.

        @param e: the backend object
        @returns an AST
        '''
        raise BackendError("backend %s doesn't implement abstract()" % self.__class__.__name__)

    #
    # These functions simplify expressions.
    #

    def simplify(self, e):
        return self.abstract(self._simplify(self.convert(e)))

    def _simplify(self, e): # pylint:disable=R0201,unused-argument
        raise BackendError("backend %s can't simplify" % self.__class__.__name__)

from .ast.base import Base
from .operations import opposites
from .errors import BackendError, ClaripyRecursionError
