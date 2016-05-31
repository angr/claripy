import sys
import ctypes
import weakref
import threading

import logging
l = logging.getLogger('claripy.backend')

class Backend(object):
    """
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
    """


    def __init__(self, solver_required=None):
        self._op_raw = { }
        self._op_raw_result = { } # these are operations that work on raw objects and accept a result arg
        self._op_expr = { }
        self._cache_objects = True
        self._solver_required = solver_required is not None

        self._tls = threading.local()
        self._true_cache = weakref.WeakKeyDictionary()
        self._false_cache = weakref.WeakKeyDictionary()

    @property
    def _object_cache(self):
        try:
            return self._tls.object_cache
        except AttributeError:
            self._tls.object_cache = weakref.WeakKeyDictionary()
            return self._tls.object_cache

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
        """
        Fill up `self._op_expr` dict.

        :param op_list:     A list of operation names.
        :param op_dict:     A dictionary of operation methods.
        :param op_class:    Where the operation method comes from.
        :return:
        """
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
        """
        Converts `r` to something usable by this backend.
        """
        return r

    def downsize(self):
        """
        Clears all caches associated with this backend.
        """
        self._object_cache.clear()
        self._true_cache.clear()
        self._false_cache.clear()

    def handles(self, expr, result=None):
        """
        Checks whether this backend can handle the expression.

        :param expr:    The expression.
        :param result:  A Result object (for concrete-only symbolic evaluation).
        :return:        True if the backend can handle this expression, False if not.
        """
        try:
            self.convert(expr, result=result)
            return True
        except BackendError:
            return False

    def convert(self, expr, result=None): #pylint:disable=R0201
        """
        Resolves a claripy.Base into something usable by the backend.

        :param expr:    The expression.
        :param save:    Save the result in the expression's object cache
        :param result:  A Result object (for concrete-only symbolic evaluation).
        :return:        A backend object.
        """
        if isinstance(expr, Base):
            # if we have a result, and it's cached there, use it
            if result is not None:
                try: return result.resolve_cache[self][expr._cache_key]
                except KeyError: pass

            # otherwise, if it's cached in the backend, use it
            try: return self._object_cache[expr._cache_key]
            except KeyError: pass

            # if we've errroed on this in the past, give up
            if self in expr._errored and result is None:
                raise BackendError("%s can't handle operation %s (%s) due to a failed conversion on a child node" % (self, expr.op, expr.__class__.__name__))

            # otherwise, resolve it!
            try:
                if expr.op in self._op_expr:
                    r = self._op_expr[expr.op](expr, result=result)
                else:
                    r = self.call(expr.op, expr.args, result=result)
            except (RuntimeError, ctypes.ArgumentError):
                e_type, value, traceback = sys.exc_info()
                raise ClaripyRecursionError, ("Recursion limit reached. I sorry.", e_type, value), traceback
            except BackendError:
                expr._errored.add(self)
                raise

            # apply the annotations
            for a in expr.annotations:
                r = self.apply_annotation(r, a)

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

    def call(self, op, args, result=None):
        """
        Calls operation `op` on args `args` with this backend.

        :return:   A backend object representing the result.
        """
        converted = self.convert_list(args, result=result)

        if op in self._op_raw_result:
            obj = self._op_raw_result[op](*converted, result=result)
        elif op in self._op_raw:
            # the raw ops don't get the model, cause, for example, Z3 stuff can't take it
            obj = self._op_raw[op](*converted)
        elif not op.startswith("__"):
            l.debug("backend has no operation %s", op)
            raise BackendError("backend has no operation %s" % op)
        else:
            obj = NotImplemented

            # first, try the operation with the first guy
            if hasattr(converted[0], op):
                op_func = getattr(converted[0], op)
                obj = op_func(*converted[1:])
            # now try the reverse operation with the second guy
            if obj is NotImplemented and len(converted) == 2 and hasattr(converted[1], opposites[op]):
                op_func = getattr(converted[1], opposites[op])
                obj = op_func(converted[0])

        if obj is NotImplemented:
            l.debug("received NotImplemented in %s.call() for operation %s", self, op)
            raise BackendError("%s can't apply operation %s" % (self, op))

        return obj

    #
    # Abstraction and resolution.
    #

    def _abstract(self, e): #pylint:disable=W0613,R0201
        """
        Abstracts the BackendObject e to an AST.

        :param e:   The backend object.
        :return:   An AST.
        """
        raise BackendError("backend %s doesn't implement abstract()" % self.__class__.__name__)

    #
    # These functions simplify expressions.
    #

    def simplify(self, e):
        o = self._abstract(self._simplify(self.convert(e)))
        o._simplified = Base.FULL_SIMPLIFY
        return o

    def _simplify(self, e): # pylint:disable=R0201,unused-argument
        raise BackendError("backend %s can't simplify" % self.__class__.__name__)

    #
    # Some other helpers
    #

    def is_true(self, e, extra_constraints=(), result=None, solver=None): #pylint:disable=unused-argument
        """
        Should return True if `e` can be easily found to be True.

        :param e:                   The AST.
        :param extra_constraints:   Extra constraints (claripy.E objects) to add to the solver for this solve.
        :param result:              The result of the previous solve.
        :param solver:              A solver, for backends that require it.
        :returns:                   A boolean.
        """

        #if self._solver_required and solver is None:
        #   raise BackendError("%s requires a solver for evaluation" % self.__class__.__name__)
        if not isinstance(e, Base):
            return self._is_true(self.convert(e), extra_constraints=extra_constraints, result=result, solver=solver)

        try:
            return self._true_cache[e.cache_key]
        except KeyError:
            t = self._is_true(self.convert(e), extra_constraints=extra_constraints, result=result, solver=solver)
            self._true_cache[e.cache_key] = t
            if t is True:
                self._false_cache[e.cache_key] = False
            return t

    def is_false(self, e, extra_constraints=(), result=None, solver=None): #pylint:disable=unused-argument
        """
        Should return True if e can be easily found to be False.

        :param e:                   The AST
        :param extra_constraints:   Extra constraints (claripy.E objects) to add to the solver for this solve.
        :param result:              The result of the previous solve
        :param solver:              A solver, for backends that require it
        :return:                   A boolean.
        """

        #if self._solver_required and solver is None:
        #   raise BackendError("%s requires a solver for evaluation" % self.__class__.__name__)
        if not isinstance(e, Base):
            return self._is_false(self.convert(e), extra_constraints=extra_constraints, result=result, solver=solver)

        try:
            return self._false_cache[e.cache_key]
        except KeyError:
            f = self._is_false(self.convert(e), extra_constraints=extra_constraints, result=result, solver=solver)
            self._false_cache[e.cache_key] = f
            if f is True:
                self._true_cache[e.cache_key] = False
            return f

    def _is_false(self, e, extra_constraints=(), result=None, solver=None): #pylint:disable=no-self-use,unused-argument
        """
        The native version of is_false.

        :param e:                   The backend object.
        :param extra_constraints:   Extra constraints (claripy.E objects) to add to the solver for this solve.
        :param result:              The result of the previous solve.
        :param solver:              A solver, for backends that require it.
        :return:                   A boolean.
        """
        raise BackendError("backend doesn't support _is_false")

    def _is_true(self, e, extra_constraints=(), result=None, solver=None): #pylint:disable=no-self-use,unused-argument
        """
        The native version of is_true.

        :param e:                   The backend object.
        :param extra_constraints:   Extra constraints (claripy.E objects) to add to the solver for this solve.
        :param result:              The result of the previous solve.
        :param solver:              A solver, for backends that require it.
        :return:                   A boolean.
        """
        raise BackendError("backend doesn't support _is_true")

    def has_true(self, e, extra_constraints=(), result=None, solver=None): #pylint:disable=unused-argument
        """
        Should return True if `e` can possible be True.

        :param e:                   The AST.
        :param extra_constraints:   Extra constraints (claripy.E objects) to add to the solver for this solve.
        :param result:              The result of the previous solve.
        :param solver:              A solver, for backends that require it.
        :return:                   A boolean
        """

        #if self._solver_required and solver is None:
        #   raise BackendError("%s requires a solver for evaluation" % self.__class__.__name__)

        return self._has_true(self.convert(e), extra_constraints=extra_constraints, result=result, solver=solver)

    def has_false(self, e, extra_constraints=(), result=None, solver=None): #pylint:disable=unused-argument
        """
        Should return False if `e` can possibly be False.

        :param e:                   The AST.
        :param extra_constraints:   Extra constraints (claripy.E objects) to add to the solver for this solve.
        :param result:              The result of the previous solve.
        :param solver:              A solver, for backends that require it.
        :return:                   A boolean.
        """

        #if self._solver_required and solver is None:
        #   raise BackendError("%s requires a solver for evaluation" % self.__class__.__name__)

        return self._has_false(self.convert(e), extra_constraints=extra_constraints, result=result, solver=solver)

    def _has_false(self, e, extra_constraints=(), result=None, solver=None): #pylint:disable=no-self-use,unused-argument
        """
        The native version of :func:`has_false`.

        :param e:                   The backend object.
        :param extra_constraints:   Extra constraints (claripy.E objects) to add to the solver for this solve.
        :param result:              The result of the previous solve.
        :param solver:              A solver, for backends that require it.
        :return:                   A boolean.
        """
        raise BackendError("backend doesn't support _has_false")

    def _has_true(self, e, extra_constraints=(), result=None, solver=None): #pylint:disable=no-self-use,unused-argument
        """
        The native version of :func:`has_true`.

        :param e:                   The backend object.
        :param extra_constraints:   Extra constraints (claripy.E objects) to add to the solver for this solve.
        :param result:              The result of the previous solve.
        :param solver:              A solver, for backends that require it.
        :return:                   A boolean.
        """
        raise BackendError("backend doesn't support _has_true")

    #
    # These functions are straight-up solver functions
    #

    def solver(self, timeout=None): #pylint:disable=no-self-use,unused-argument
        """
        This function should return an instance of whatever object handles
        solving for this backend. For example, in Z3, this would be z3.Solver().
        """
        raise BackendError("backend doesn't support solving")

    def add(self, s, c):
        """
        This function adds constraints to the backend solver.

        :param c: A sequence of claripy.E objects.
        :param s: A backend solver object.
        """
        return self._add(s, self.convert_list(c))

    def _add(self, s, c): #pylint:disable=no-self-use,unused-argument
        """
        This function adds constraints to the backend solver.

        :param c: sequence of converted backend objects
        :param s: backend solver object
        """
        raise BackendError("backend doesn't support solving")

    def check(self, s, extra_constraints=()):
        """
        This function does a constraint check.

        :param s:                   The backend solver object.
        :param extra_constraints:   Extra constraints (claripy.E objects) to add to s for this solve.
        :return:                   True or False, depending on satisfiability.
        """
        return self._check(s, extra_constraints=self.convert_list(extra_constraints))

    def _check(self, s, extra_constraints=()): #pylint:disable=no-self-use,unused-argument
        """
        This function does a constraint check.

        :param s:                   The backend solver object.
        :param extra_constraints:   Extra constraints (backend objects) to add to s for this solve.
        :returns                    True or False, depending on satisfiability.
        """
        raise BackendError("backend doesn't support solving")

    def results(self, s, extra_constraints=(), generic_model=None):
        """
        This function does a constraint check.

        :param s:                   The backend solver object.
        :param extra_constraints:   Extra constraints (claripy.E objects) to add to s for this solve
        :param generic_model:       Whether or not to create a generic model
        :return:                   A Result object
        """
        return self._results(s, extra_constraints=self.convert_list(extra_constraints), generic_model=generic_model)

    def _results(self, s, extra_constraints=(), generic_model=None): #pylint:disable=no-self-use,unused-argument
        """
        This function does a constraint check.

        :param s:                   The backend solver object
        :param extra_constraints:   Extra constraints (backend objects) to add to s for this solve
        :param generic_model:       Whether or not to create a generic model
        :return:                   A Result object
        """
        raise BackendError("backend doesn't support solving")

    #
    # These functions provide evaluation support.
    #

    def eval(self, expr, n, result=None, extra_constraints=(), solver=None):
        """
        This function returns up to `n` possible solutions for expression `expr`.

        :param expr: expression (claripy.E object) to evaluate
        :param n: number of results to return
        :param result: a cached Result from the last constraint solve
        :param solver: a solver object, native to the backend, to assist in
                       the evaluation (for example, a z3.Solver)
        :param extra_constraints: extra constraints (claripy.E objects) to add
                                  to the solver for this solve
        :return:              A sequence of up to n results (backend objects)
        """
        if self._solver_required and solver is None:
            raise BackendError("%s requires a solver for evaluation" % self.__class__.__name__)

        return self._eval(self.convert(expr, result=result if n == 1 else None), n, result=result, extra_constraints=self.convert_list(extra_constraints, result=result), solver=solver)

    def _eval(self, expr, n, result=None, extra_constraints=(), solver=None): #pylint:disable=unused-argument,no-self-use
        """
        This function returns up to `n` possible solutions for expression `expr`.

        :param expr:                An expression (backend object) to evaluate.
        :param n:                   A number of results to return.
        :param result:              A cached Result from the last constraint solve.
        :param extra_constraints:   Extra constraints (claripy.E objects) to add to the solver for this solve.
        :param solver:              A solver object, native to the backend, to assist in the evaluation (for example, a
                                    z3.Solver).
        :return:                    A sequence of up to n results (backend objects).
        """
        raise BackendError("backend doesn't support eval()")

    def batch_eval(self, exprs, n, result=None, extra_constraints=(), solver=None):
        """
        Evaluate one or multiple expressions.

        :param exprs:               A list of expressions to evaluate.
        :param n:                   Number of different solutions to return.
        :param result:              A cached Result from the last constraint solve.
        :param extra_constraints:   Extra constraints (claripy.E objects) to add to the solver for this solve.
        :param solver:              A solver object, native to the backend, to assist in the evaluation.
        :return:                    A list of up to n tuples, where each tuple is a solution for all expressions.
        """
        if self._solver_required and solver is None:
            raise BackendError("%s requires a solver for batch evaluation" % self.__class__.__name__)

        converted_exprs = [ self.convert(ex, result=result if n == 1 else None) for ex in exprs ]

        return self._batch_eval(converted_exprs, n, result=result, extra_constraints=self.convert_list(extra_constraints, result=result), solver=solver)

    def _batch_eval(self, exprs, n, result=None, extra_constraints=(), solver=None): #pylint:disable=unused-argument,no-self-use
        """
        Evaluate one or multiple expressions.

        :param exprs:               A list of expressions to evaluate.
        :param n:                   Number of different solutions to return.
        :param result:              A cached Result from the last constraint solve.
        :param extra_constraints:   Extra constraints (claripy.E objects) to add to the solver for this solve.
        :param solver:              A solver object, native to the backend, to assist in the evaluation.
        :return:                    A list of up to n tuples, where each tuple is a solution for all expressions.
        """

        raise BackendError("backend doesn't support batch_eval()")

    def min(self, expr, result=None, extra_constraints=(), solver=None):
        """
        Return the minimum value of `expr`.

        :param expr: expression (claripy.E object) to evaluate
        :param result: a cached Result from the last constraint solve
        :param solver: a solver object, native to the backend, to assist in
                       the evaluation (for example, a z3.Solver)
        :param extra_constraints: extra constraints (claripy.E objects) to add
                                  to the solver for this solve
        :return: the minimum possible value of expr (backend object)
        """
        if self._solver_required and solver is None:
            raise BackendError("%s requires a solver for evaluation" % self.__class__.__name__)

        return self._min(self.convert(expr), result=result, extra_constraints=self.convert_list(extra_constraints, result=result), solver=solver)

    def _min(self, expr, result=None, extra_constraints=(), solver=None): #pylint:disable=unused-argument,no-self-use
        """
        Return the minimum value of expr.

        :param expr: expression (backend object) to evaluate
        :param result: a cached Result from the last constraint solve
        :param solver: a solver object, native to the backend, to assist in
                       the evaluation (for example, a z3.Solver)
        :param extra_constraints: extra constraints (claripy.E objects) to add
                                  to the solver for this solve
        :return: the minimum possible value of expr (backend object)
        """
        raise BackendError("backend doesn't support min()")

    def max(self, expr, result=None, extra_constraints=(), solver=None):
        """
        Return the maximum value of expr.

        :param expr: expression (claripy.E object) to evaluate
        :param result: a cached Result from the last constraint solve
        :param solver: a solver object, native to the backend, to assist in
                       the evaluation (for example, a z3.Solver)
        :param extra_constraints: extra constraints (claripy.E objects) to add
                                  to the solver for this solve
        :return: the maximum possible value of expr (backend object)
        """
        if self._solver_required and solver is None:
            raise BackendError("%s requires a solver for evaluation" % self.__class__.__name__)

        return self._max(self.convert(expr), result=result, extra_constraints=self.convert_list(extra_constraints, result=result), solver=solver)

    def _max(self, expr, result=None, extra_constraints=(), solver=None): #pylint:disable=unused-argument,no-self-use
        """
        Return the maximum value of expr.

        :param expr: expression (backend object) to evaluate
        :param result: a cached Result from the last constraint solve
        :param solver: a solver object, native to the backend, to assist in
                       the evaluation (for example, a z3.Solver)
        :param extra_constraints: extra constraints (claripy.E objects) to add
                                  to the solver for this solve
        :return: the maximum possible value of expr (backend object)
        """
        raise BackendError("backend doesn't support max()")

    def min_values(self, expr, result=None, extra_constraints=(), solver=None):
        """
        Return a set of values of expr, in which the minimum is present.
        This is an optimization for performing less constraint solving.

        :param expr: expression (claripy.E object) to evaluate
        :param result: a cached Result from the last constraint solve
        :param solver: a solver object, native to the backend, to assist in
                       the evaluation (for example, a z3.Solver)
        :param extra_constraints: extra constraints (claripy.E objects) to add
                                  to the solver for this solve
        :return: the minimum possible value of expr (backend object)
        """
        if self._solver_required and solver is None:
            raise BackendError("%s requires a solver for evaluation" % self.__class__.__name__)

        return self._min_values(self.convert(expr), result=result, extra_constraints=self.convert_list(extra_constraints, result=result), solver=solver)

    def _min_values(self, expr, result=None, extra_constraints=(), solver=None): #pylint:disable=unused-argument,no-self-use
        """
        Return a set of values of expr, in which the minimum is present.
        This is an optimization for performing less constraint solving.

        :param expr: expression (backend object) to evaluate
        :param result: a cached Result from the last constraint solve
        :param solver: a solver object, native to the backend, to assist in
                       the evaluation (for example, a z3.Solver)
        :param extra_constraints: extra constraints (claripy.E objects) to add
                                  to the solver for this solve
        :return: the minimum possible value of expr (backend object)
        """
        raise BackendError("backend doesn't support min_values()")

    def max_values(self, expr, result=None, extra_constraints=(), solver=None):
        """
        Return a set of values of expr, in which the maximum is present.
        This is an optimization for performing less constraint solving.

        :param expr: expression (claripy.E object) to evaluate
        :param result: a cached Result from the last constraint solve
        :param solver: a solver object, native to the backend, to assist in
                       the evaluation (for example, a z3.Solver)
        :param extra_constraints: extra constraints (claripy.E objects) to add
                                  to the solver for this solve
        :return: the maximum possible value of expr (backend object)
        """
        if self._solver_required and solver is None:
            raise BackendError("%s requires a solver for evaluation" % self.__class__.__name__)

        return self._max_values(self.convert(expr), result=result, extra_constraints=self.convert_list(extra_constraints, result=result), solver=solver)

    def _max_values(self, expr, result=None, extra_constraints=(), solver=None): #pylint:disable=unused-argument,no-self-use
        """
        Return a set of values of expr, in which the maximum is present.
        This is an optimization for performing less constraint solving.

        :param expr: expression (backend object) to evaluate
        :param result: a cached Result from the last constraint solve
        :param solver: a solver object, native to the backend, to assist in
                       the evaluation (for example, a z3.Solver)
        :param extra_constraints: extra constraints (claripy.E objects) to add
                                  to the solver for this solve
        :return: the maximum possible value of expr (backend object)
        """
        raise BackendError("backend doesn't support max_values()")

    def solution(self, expr, v, result=None, extra_constraints=(), solver=None):
        """
        Return True if `v` is a solution of `expr` with the extra constraints, False otherwise.

        :param expr:                An expression (claripy.E) to evaluate
        :param v:                   The proposed solution (claripy.E)
        :param result:              A cached Result from the last constraint solve
        :param solver:              A solver object, native to the backend, to assist in the evaluation (for example,
                                    a z3.Solver).
        :param extra_constraints:   Extra constraints (claripy.E objects) to add to the solver for this solve.
        :return:                   True if `v` is a solution of `expr`, False otherwise
        """
        if self._solver_required and solver is None:
            raise BackendError("%s requires a solver for evaluation" % self.__class__.__name__)

        return self._solution(self.convert(expr), self.convert(v), result=result, extra_constraints=self.convert_list(extra_constraints, result=result), solver=solver)

    def _solution(self, expr, v, result=None, extra_constraints=(), solver=None): #pylint:disable=unused-argument,no-self-use
        """
        Return True if v is a solution of expr with the extra constraints, False otherwise.

        :param expr: expression (backend object) to evaluate
        :param v: the proposed solution (backend object)
        :param result: a cached Result from the last constraint solve
        :param solver: a solver object, native to the backend, to assist in
                       the evaluation (for example, a z3.Solver)
        :param extra_constraints: extra constraints (claripy.E objects) to add
                                  to the solver for this solve
        :return: True if v is a solution of expr, False otherwise
        """

        raise BackendError("backend doesn't support solution()")

    #
    # Some other methods
    #

    def size(self, a, result=None):
        """
        This should return the size of an expression.

        :param a: the claripy A object
        """
        return self._size(self.convert(a, result=result))

    def _size(self, o, result=None): #pylint:disable=no-self-use,unused-argument
        """
        This should return the size of an object.

        :param o: the (backend-native) object
        """
        raise BackendError("backend doesn't support size()")

    def name(self, a, result=None):
        """
        This should return the name of an expression.

        :param a: the claripy A object
        """
        return self._name(self.convert(a, result=result))

    def _name(self, o, result=None): #pylint:disable=no-self-use,unused-argument
        """
        This should return the name of an object.

        :param o: the (backend-native) object
        """
        raise BackendError("backend doesn't support name()")

    def identical(self, a, b, result=None):
        """
        This should return whether `a` is identical to `b`. Of course, this isn't always clear. True should mean that it
        is definitely identical. False eans that, conservatively, it might not be.

        :param a: a claripy A object
        :param b: a claripy A object
        """
        return self._identical(self.convert(a, result=result), self.convert(b, result=result))

    def _identical(self, a, b, result=None): #pylint:disable=no-self-use,unused-argument
        """
        This should return whether `a` is identical to `b`. This is the native version of ``identical()``.

        :param a: the (backend-native) object
        :param b: the (backend-native) object
        """
        raise BackendError("backend doesn't support identical()")

    def cardinality(self, a, result=None):
        """
        This should return the maximum number of values that an expression can take on. This should be a strict *over*
        approximation.

        :param a:   A claripy A object.
        :return:    An integer.
        """
        return self._cardinality(self.convert(a, result=result))

    def _cardinality(self, b, result=None): #pylint:disable=no-self-use,unused-argument
        """
        This should return the maximum number of values that an expression can take on. This should be a strict
        *over* approximation.

        :param a:   A claripy A object.
        :return:    An integer.
        """
        raise BackendError("backend doesn't support cardinality()")

    def singlevalued(self, a, result=None):
        return self.cardinality(a, result=result) == 1

    def multivalued(self, a, result=None):
        return self.cardinality(a, result=result) > 1

    def apply_annotation(self, o, a): #pylint:disable=no-self-use,unused-argument
        """
        This should apply the annotation on the backend object, and return a new backend object.

        :param o: A backend object.
        :param a: An Annotation object.
        :return: A backend object.
        """
        return o

from .ast.base import Base
from .operations import opposites
from .errors import BackendError, ClaripyRecursionError
