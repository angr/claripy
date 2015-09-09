#!/usr/bin/env python

import logging
l = logging.getLogger("claripy.frontends.frontend")

import ana

#pylint:disable=unidiomatic-typecheck

class Frontend(ana.Storable):
    def __init__(self, solver_backend):
        self._solver_backend = solver_backend
        self.result = None
        self._simplified = False

    #
    # Storable support
    #

    @property
    def uuid(self):
        return self.ana_uuid

    def _ana_getstate(self):
        if not self._simplified: self.simplify()
        return self._solver_backend.__class__.__name__, self.result

    def _ana_setstate(self, s):
        solver_backend_name, self.result = s
        self._solver_backend = _backends[solver_backend_name]
        self._simplified = True

    #
    # Constraint management
    #

    @staticmethod
    def _split_constraints(constraints):
        '''
        Returns independent constraints, split from this Frontend's constraints.
        '''

        splitted = [ ]
        for i in constraints:
            splitted.extend(i.split(['And']))

        l.debug("... splitted of size %d", len(splitted))

        variable_connections = { }
        constraint_connections = { }
        for n,s in enumerate(splitted):
            l.debug("... processing constraint with %d variables", len(s.variables))

            connected_variables = set(s.variables)
            connected_constraints = { n }

            if len(connected_variables) == 0:
                connected_variables.add('CONCRETE')

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
        fc = [ ]
        for e in ec if type(ec) in (list, tuple, set) else (ec,):
            #e_simp = self._claripy.simplify(e)
            e_simp = e
            for b in _eager_backends + [ self._solver_backend ]:
                try:
                    o = b.convert(e_simp)
                    if b._is_false(o):
                        #filter_false += 1
                        raise UnsatError("expressions contain False")
                    elif b._has_true(o):
                        #filter_true +=1
                        break
                    else:
                        l.warning("Frontend._constraint_filter got non-boolean from model_backend")
                        raise ClaripyFrontendError()
                except BackendError:
                    pass
            else:
                fc.append(e_simp)

        return tuple(fc)

    def branch(self):
        s = self.__class__(self._solver_backend)
        s.result = self.result
        s._simplified = self._simplified
        return s

    #
    # Stuff that should be implemented by subclasses
    #

    def _add_constraints(self, constraints, invalidate_cache=True):
        raise NotImplementedError("_add_constraints() is not implemented")

    def _simplify(self):
        raise NotImplementedError("_simplify() is not implemented")

    def _solve(self, extra_constraints=()):
        raise NotImplementedError("_solve() is not implemented")

    def _eval(self, e, n, extra_constraints=()):
        raise NotImplementedError("_eval() is not implemented")

    def _min(self, e, extra_constraints=()):
        raise NotImplementedError("_min() is not implemented")

    def _max(self, e, extra_constraints=()):
        raise NotImplementedError("_max() is not implemented")

    def _solution(self, e, v, extra_constraints=()):
        raise NotImplementedError("_solution() is not implemented")

    def finalize(self):
        raise NotImplementedError("finalize() is not implemented")

    def merge(self, others, merge_flag, merge_values):
        raise NotImplementedError("merge() is not implemented")

    def combine(self, others):
        raise NotImplementedError("combine() is not implemented")

    def split(self):
        raise NotImplementedError("split() is not implemented")

    #
    # Solving
    #

    def add(self, constraints, invalidate_cache=True):
        if type(constraints) not in (list, tuple):
            constraints = [ constraints ]

        if len(constraints) == 0:
            return [ ]

        try:
            to_add = self._constraint_filter(constraints)
        except UnsatError:
            self.result = UnsatResult()
            to_add = [ false ]

        for c in to_add:
            c.make_uuid()
            if not isinstance(c, Bool):
                raise ClaripyTypeError('constraint is not a boolean expression!')

        if self.result is not None and invalidate_cache:
            all_true = True
            for c in to_add:
                try:
                    v = LightFrontend._eval.im_func(self, c, 1)[0]
                    all_true &= v
                except ClaripyFrontendError:
                    all_true = False
                    break
        else:
            all_true = False

        self._add_constraints(to_add, invalidate_cache=invalidate_cache)
        self._simplified = False

        if invalidate_cache and self.result is not None and self.result.sat:
            if all_true:
                new_result = SatResult()
                new_result.model.update(self.result.model)
                self.result = new_result
            else:
                self.result = None

        return to_add

    def simplify(self):
        if self._simplified:
            return

        s = self._simplify()
        self._simplified = True
        return s

    def solve(self, extra_constraints=()):
        l.debug("%s.solve() running with %d extra constraints...", self.__class__.__name__, len(extra_constraints))

        if self.result is not None:
            if not self.result.sat or len(extra_constraints) == 0:
                l.debug("... returning cached result (sat: %s)", self.result.sat)
                return self.result
        else:
            l.debug("... no cached result")

        try:
            extra_constraints = self._constraint_filter(extra_constraints)
        except UnsatError:
            l.debug("... returning unsat result due to false extra_constraints")
            return UnsatResult()

        l.debug("... conferring with the solver")
        r = self._solve(extra_constraints=extra_constraints)
        if len(extra_constraints) == 0 or (self.result is None and r.sat):
            l.debug("... caching result (sat: %s)", r.sat)
            self.result = r
        return r

    def satisfiable(self, extra_constraints=()):
        return self.solve(extra_constraints=extra_constraints).sat

    def eval(self, e, n, extra_constraints=()):
        extra_constraints = self._constraint_filter(extra_constraints)

        if not isinstance(e, Base):
            raise ValueError("Expressions passed to eval() MUST be Claripy ASTs (got %s)" % type(e))

        return self._eval(e, n, extra_constraints=extra_constraints)

    def max(self, e, extra_constraints=()):
        extra_constraints = self._constraint_filter(extra_constraints)

        if not isinstance(e, Base):
            raise ValueError("Expressions passed to max() MUST be Claripy ASTs (got %s)" % type(e))

        if len(extra_constraints) == 0 and self.result is not None and e.uuid in self.result.max_cache:
            #cached_max += 1
            return self.result.max_cache[e.uuid]

        m = self._max(e, extra_constraints=extra_constraints)
        if len(extra_constraints) == 0 and e.symbolic:
            if self.result is not None: self.result.max_cache[e.uuid] = m
            self.add([ULE(e, m)], invalidate_cache=False)
        return m

    def min(self, e, extra_constraints=()):
        extra_constraints = self._constraint_filter(extra_constraints)

        if not isinstance(e, Base):
            raise ValueError("Expressions passed to min() MUST be Claripy ASTs (got %s)" % type(e))

        if len(extra_constraints) == 0 and self.result is not None and e.uuid in self.result.min_cache:
            #cached_min += 1
            return self.result.min_cache[e.uuid]

        m = self._min(e, extra_constraints=extra_constraints)
        if len(extra_constraints) == 0 and e.symbolic:
            if self.result is not None: self.result.min_cache[e.uuid] = m
            self.add([UGE(e, m)], invalidate_cache=False)
        return m

    def solution(self, e, v, extra_constraints=()):
        try:
            extra_constraints = self._constraint_filter(extra_constraints)
        except UnsatError:
            return False

        if not isinstance(e, Base):
            raise ValueError("Expressions passed to solution() MUST be Claripy ASTs (got %s)" % type(e))

        b = self._solution(e, v, extra_constraints=extra_constraints)
        if b is False and len(extra_constraints) > 0 and e.symbolic:
            self.add([e != v], invalidate_cache=False)
        return b

    #
    # Serialization and such.
    #

    def downsize(self): #pylint:disable=R0201
        if self.result is not None:
            self.result.downsize()

from .frontends import LightFrontend
from .result import UnsatResult, SatResult
from .errors import UnsatError, BackendError, ClaripyFrontendError, ClaripyTypeError
from . import _eager_backends, _backends
from .ast.base import Base
from .ast.bool import false, Bool
from .ast.bv import UGE, ULE
