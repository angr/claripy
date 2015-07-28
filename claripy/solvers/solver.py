#!/usr/bin/env python

import logging
l = logging.getLogger("claripy.solvers.solver")

import sys

import time
l_timing = logging.getLogger("claripy.solvers.solver_timing")

cached_evals = 0
cached_min = 0
cached_max = 0
cached_solve = 0
filter_true = 0
filter_false = 0

import ana

#pylint:disable=unidiomatic-typecheck

class Solver(ana.Storable):
    def __init__(self, solver_backend, result=None, timeout=None, solver=None, to_add=None):
        self._finalized = None
        self._result = result
        self._simplified = True
        self._timeout = timeout if timeout is not None else 300000
        self._backend_uses_solver = True

        # solving
        self._solver_backend = solver_backend
        self._solver = solver
        self._to_add = [ ] if to_add is None else to_add

        # constraints
        try:
            self.constraints = [ ]
            self.variables = set()
        except AttributeError:
            pass

    #
    # Storable support
    #

    @property
    def uuid(self): return self.ana_uuid

    def _ana_getstate(self):
        if not self._simplified: self.simplify()
        return self._result, self._timeout, self.constraints, self.variables

    def _ana_setstate(self, s):
        self._simplified = True
        r, to, c, v = s
        self.__init__(result=r, timeout=to)
        self.constraints = c
        self.variables = v

    #
    # Solver Creation
    #

    def _get_solver(self):
        if not self._backend_uses_solver:
            return None

        if self._solver is None:
            try:
                self._solver = self._solver_backend.solver(timeout=self._timeout)
            except BackendError:
                self._backend_uses_solver = False
                return None
            self._solver_backend.add(self._solver, self.constraints)

        self._solver_backend.add(self._solver, self._to_add)
        self._to_add = [ ]
        return self._solver

    #
    # Constraint management
    #

    def _independent_constraints(self, constraints=None):
        '''
        Returns independent constraints, split from this Solver's constraints.
        '''

        splitted = [ ]
        for i in self.constraints if constraints is None else constraints: #pylint:disable=E1101
            splitted.extend(i.split(['And']))

        l.debug("... splitted of size %d", len(splitted))

        variable_connections = { }
        constraint_connections = { }
        for n,s in enumerate(splitted):
            l.debug("... processing constraint with %d variables", len(s.variables))

            connected_variables = set(s.variables)
            connected_constraints = { n }

            if len(connected_variables) == 0:
                connected_variables.add('CONSTANT')

            for v in s.variables:
                if v in variable_connections:
                    connected_variables |= variable_connections[v]
                if v in constraint_connections:
                    connected_constraints |= constraint_connections[v]

            for v in connected_variables:
                variable_connections[v] = connected_variables
                constraint_connections[v] = connected_constraints

        unique_constraint_sets = set()
        for v in variable_connections:
            unique_constraint_sets.add((frozenset(variable_connections[v]), frozenset(constraint_connections[v])))

        results = [ ]
        for v,c_indexes in unique_constraint_sets:
            results.append((set(v), [ splitted[c] for c in c_indexes ]))
        return results

    def _constraint_filter(self, ec):
        global filter_true, filter_false

        fc = [ ]
        for e in ec if type(ec) in (list, tuple, set) else (ec,):
            #e_simp = self._claripy.simplify(e)
            e_simp = e
            for b in _eager_backends + [ self._solver_backend ]:
                try:
                    o = b.convert(e_simp)
                    if b.is_false(o):
                        filter_false += 1
                        raise UnsatError("expressions contain False")
                    elif b.has_true(o):
                        filter_true +=1
                        break
                    else:
                        l.warning("Solver._constraint_filter got non-boolean from model_backend")
                        raise ClaripySolverError()
                except BackendError:
                    pass
            else:
                fc.append(e_simp)

        return tuple(fc)

    def add(self, constraints, invalidate_cache=True):
        if type(constraints) not in (list, tuple):
            constraints = [ constraints ]

        if len(constraints) == 0:
            return None

        if type(constraints[0]) in (list, tuple):
            raise ValueError("don't pass lists to Solver.add()!")

        try:
            to_add = self._constraint_filter(constraints)
            if len(to_add) > 0 and invalidate_cache:
                self._result = None
        except UnsatError:
            to_add = [ false ]
            self._result = Result(False, { })

        if len(to_add) > 0:
            # generate UUIDs for every constraint
            for c in to_add:
                c.make_uuid()
                if c.length is not None:
                    raise ClaripyTypeError('constraint is not a boolean expression!')

            self._simplified = False
            self.constraints += to_add

            for e in to_add:
                self.variables.update(e.variables)

            self._to_add += to_add

    def simplify(self):
        if self._simplified or len(self.constraints) == 0: return
        self.constraints = [ simplify(And(*self.constraints)) ]

        # generate UUIDs for every constraint
        for c in self.constraints:
            if isinstance(c, Base): c.make_uuid()

        self._solver = None
        self._to_add = [ ]
        self._simplified = True

        return self.constraints

    #
    # Solving
    #

    def solve(self, extra_constraints=()):
        global cached_solve
        try:
            extra_constraints = self._constraint_filter(extra_constraints)
        except UnsatError:
            return Result(False, { })

        if self._result is not None and not self._result.sat:
            return self._result

        if len(extra_constraints) == 0 and self._result is not None:
            cached_solve += 1
            return self._result
        else:
            r = self._solve(extra_constraints=extra_constraints)
            if r.sat or len(extra_constraints) == 0:
                self._result = r
            return r

    def satisfiable(self, extra_constraints=()):
        return self.solve(extra_constraints=extra_constraints).sat

    def any(self, expr, extra_constraints=()):
        v = self.eval(expr, 1, extra_constraints)
        if len(v) == 0:
            raise UnsatError("couldn't concretize any values")
        return v[0]

    def eval(self, e, n, extra_constraints=()):
        global cached_evals
        extra_constraints = self._constraint_filter(extra_constraints)

        if not isinstance(e, Base): raise ValueError("Solver got a non-E for e.")

        if len(extra_constraints) == 0:
            for b in _eager_backends:
                try: return b.eval(e, n, result=self._result)
                except BackendError: pass

        if not self.satisfiable(extra_constraints=extra_constraints): raise UnsatError('unsat')

        l.debug("Solver.eval() for UUID %s with n=%d and %d extra_constraints", e.uuid, n, len(extra_constraints))

        if len(extra_constraints) == 0 and e.uuid in self._result.eval_cache:
            cached_results = self._result.eval_cache[e.uuid][1]
            cached_n = self._result.eval_cache[e.uuid][0]

            if cached_n >= n or len(cached_results) < cached_n:
                cached_evals += min(len(cached_results), n)
                # sort so the order of results is consistent when using pypy
                return tuple(sorted(cached_results))[:n]
            else:
                solver_extra_constraints = [ e != v for v in cached_results ]
        else:
            cached_results = set()
            cached_n = 0
            solver_extra_constraints = extra_constraints

        cached_evals += cached_n
        l.debug("... %d values (of %d) were already cached.", cached_n, n)

        # if we have a cache, cached_n < n and len(cached_results) == cached_n
        all_results = cached_results
        try:
            all_results |= set(self._eval(e, n-len(all_results), extra_constraints=solver_extra_constraints))
            l.debug("... got %d more values", len(all_results) - len(cached_results))
        except UnsatError:
            l.debug("... UNSAT")
            if len(all_results) == 0:
                raise

        if len(extra_constraints) == 0:
            l.debug("... adding cache of %d values for n=%d", len(all_results), n)
            self._result.eval_cache[e.uuid] = (n, all_results)
        else:
            # can't assume that we didn't knock out other possible solutions
            l.debug("... adding cache of %d values for n=%d", len(all_results), len(all_results))
            self._result.eval_cache[e.uuid] = (len(all_results), all_results)

        # if there are less possible solutions than n (i.e., meaning we got all the solutions for e),
        # add constraints to help the solver out later
        if len(extra_constraints) == 0 and len(all_results) < n:
            l.debug("... adding constraints for %d values for future speedup", len(all_results))
            self.add([Or(*[ e == v for v in all_results ])], invalidate_cache=False)

        # sort so the order of results is consistent when using pypy
        return tuple(sorted(all_results))

    def max(self, e, extra_constraints=()):
        global cached_max
        extra_constraints = self._constraint_filter(extra_constraints)

        if len(extra_constraints) == 0:
            for b in _eager_backends:
                try: return b.max(e, result=self._result)
                except BackendError: pass

        two = self.eval(e, 2, extra_constraints=extra_constraints)
        if len(two) == 0: raise UnsatError("unsat during max()")
        elif len(two) == 1: return two[0]

        if len(extra_constraints) == 0 and e.uuid in self._result.max_cache:
            cached_max += 1
            r = self._result.max_cache[e.uuid]
        else:
            self.simplify()

            c = extra_constraints + (UGE(e, two[0]), UGE(e, two[1]))
            r = model_object(self._max(e, extra_constraints=c), result=self._result)

        if len(extra_constraints) == 0:
            self._result.max_cache[e.uuid] = r
            self.add([ULE(e, r)], invalidate_cache=False)

        return r

    def min(self, e, extra_constraints=()):
        global cached_min
        extra_constraints = self._constraint_filter(extra_constraints)

        if len(extra_constraints) == 0:
            for b in _eager_backends:
                try: return b.min(e, result=self._result)
                except BackendError: pass

        two = self.eval(e, 2, extra_constraints=extra_constraints)
        if len(two) == 0: raise UnsatError("unsat during min()")
        elif len(two) == 1: return two[0]

        if len(extra_constraints) == 0 and e.uuid in self._result.min_cache:
            cached_min += 1
            r = self._result.min_cache[e.uuid]
        else:
            self.simplify()

            c = extra_constraints + (ULE(e, two[0]), ULE(e, two[1]))
            r = model_object(self._min(e, extra_constraints=c), result=self._result)

        if len(extra_constraints) == 0:
            self._result.min_cache[e.uuid] = r
            self.add([UGE(e, r)], invalidate_cache=False)

        return r

    def solution(self, e, v, extra_constraints=()):
        try:
            extra_constraints = self._constraint_filter(extra_constraints)
        except UnsatError:
            return False

        if len(extra_constraints) == 0:
            for b in _eager_backends:
                try: return b.solution(e, v, result=self._result)
                except BackendError: pass

        b = self._solution(e, v, extra_constraints=extra_constraints)
        if b == False and len(extra_constraints) > 0:
            self.add([e != v], invalidate_cache=False)
        return b

    #
    # These are the functions that actually talk to the backends
    #

    def _solve(self, extra_constraints=()):
        # check it!
        l.debug("Solver.solve() checking SATness of %d constraints", len(self.constraints))

        if not self._solver_backend:
            # There is no solver backend. Just return True
            return Result(True, [True])

        try:
            s = self._get_solver()

            a = time.time()
            r = self._solver_backend.results(s, extra_constraints, generic_model=True)
            b = time.time()

            l_timing.debug("... %s in %s seconds", r.sat, b - a)
            return r
        except BackendError:
            e_type, value, traceback = sys.exc_info()
            raise ClaripySolverError, "Backend error during solve: %s('%s')" % (str(e_type), str(value)), traceback

    def _eval(self, e, n, extra_constraints=()):
        l.debug("solver._eval(%d) with %d extra_constraints", n, len(extra_constraints))

        try:
            results = self._solver_backend.eval(e, n, extra_constraints=extra_constraints, result=self._result, solver=self._get_solver())
            return [ model_object(r) for r in results ]
        except BackendError:
            e_type, value, traceback = sys.exc_info()
            raise ClaripySolverError, "Backend error during eval: %s('%s')" % (str(e_type), str(value)), traceback

    def _max(self, e, extra_constraints=()):
        l.debug("Solver.max() with %d extra_constraints", len(extra_constraints))
        try:
            return self._solver_backend.max(e, extra_constraints=extra_constraints, result=self._result, solver=self._get_solver())
        except BackendError:
            e_type, value, traceback = sys.exc_info()
            raise ClaripySolverError, "Backend error during _max: %s('%s')" % (str(e_type), str(value)), traceback

    def _min(self, e, extra_constraints=()):
        l.debug("Solver.min() with %d extra_constraints", len(extra_constraints))
        try:
            return self._solver_backend.min(e, extra_constraints=extra_constraints, result=self._result, solver=self._get_solver())
        except BackendError:
            e_type, value, traceback = sys.exc_info()
            raise ClaripySolverError, "Backend error during _min: %s('%s')" % (str(e_type), str(value)), traceback

    def _solution(self, e, v, extra_constraints=()):
        try:
            return self._solver_backend.solution(e, v, extra_constraints=extra_constraints, solver=self._get_solver())
        except BackendError:
            e_type, value, traceback = sys.exc_info()
            raise ClaripySolverError, "Backend error during _solution: %s('%s')" % (str(e_type), str(value)), traceback

    #
    # Serialization and such.
    #

    def downsize(self): #pylint:disable=R0201
        self._solver = { }
        self._to_add = [ ]
        if self._result is not None:
            self._result.downsize()

    #
    # Merging and splitting
    #

    def finalize(self): #pylint:disable=no-self-use
        l.error("finalize() called on a non-branching solver! This is probably a serious bug.")

    def branch(self): #pylint:disable=no-self-use
        l.error("branch() called on a non-branching solver! This is probably a serious bug.")

    def merge(self, others, merge_flag, merge_values):
        merged = self.__class__(self._solver_backend, timeout=self._timeout)
        merged._simplified = False
        options = [ ]

        for s, v in zip([self]+others, merge_values):
            options.append(And(*([ merge_flag == v ] + s.constraints)))
        merged.add([Or(*options)])

        return self._solver_backend is _backend_z3 , merged

    def combine(self, others):
        combined = self.__class__(self._solver_backend, timeout=self._timeout)
        combined._simplified = False

        combined.add(self.constraints) #pylint:disable=E1101
        for o in others:
            combined.add(o.constraints)
        return combined

    def split(self):
        results = [ ]
        l.debug("Splitting!")
        for variables,c_list in self._independent_constraints():
            l.debug("... got %d constraints with %d variables", len(c_list), len(variables))

            s = self.__class__(self._solver_backend, timeout=self._timeout)
            s._simplified = False
            s.add(c_list)
            results.append(s)
        return results

from ..result import Result
from ..errors import UnsatError, BackendError, ClaripySolverError, ClaripyTypeError
from .. import _eager_backends, _backend_z3
from ..ast_base import Base, model_object, simplify
from ..ast.bool import And, Or, false
from ..ast.bv import UGE, ULE
