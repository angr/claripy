import weakref
import itertools

class ModelCache(object):
    _defaults = { 0, 0.0, True }

    def __init__(self, model):
        self.model = model
        self.replacements = weakref.WeakKeyDictionary()

    def __hash__(self):
        if not hasattr(self, '_hash'):
            self._hash = hash(frozenset(self.model.items())) #pylint:disable=attribute-defined-outside-init
        return self._hash

    def __eq__(self, other):
        return self.model == other.model

    def __getstate__(self):
        return (self.model,)

    def __setstate__(self, s):
        self.model = s[0]
        self.replacements = weakref.WeakKeyDictionary()

    #
    # Splitting support
    #

    def filter(self, variables):
        return ModelCache({ k:v for k,v in self.model.iteritems() if k in variables })

    @staticmethod
    def combine(*models):
        return ModelCache(dict(itertools.chain.from_iterable(m.model.iteritems() for m in models)))

    #
    # Model-driven evaluation
    #

    def _leaf_op(self, a):
        return (
            all_operations.BVV(self.model.get(a.args[0], 0), a.length) if a.op == 'BVS' else
            all_operations.BoolV(self.model.get(a.args[0], True)) if a.op == 'BoolS' else
            all_operations.FPV(self.model.get(a.args[0], 0.0), a.args[1]) if a.op == 'FPS' else
            a
        )

    def eval_ast(self, ast):
        new_ast = ast._replace(self.replacements, leaf_operation=self._leaf_op)
        return backends.concrete.eval(new_ast, 1)[0]

    def eval_constraints(self, constraints):
        return all(self.eval_ast(c) for c in constraints)

    def eval_list(self, asts):
        return tuple(self.eval_ast(c) for c in asts )

class ModelCacheMixin(object):
    _MODEL_LIMIT = 257

    def __init__(self, *args, **kwargs):
        super(ModelCacheMixin, self).__init__(*args, **kwargs)
        self._models = set()
        self._exhausted = False
        self._eval_exhausted = weakref.WeakSet()
        self._max_exhausted = weakref.WeakSet()
        self._min_exhausted = weakref.WeakSet()

    def _blank_copy(self, c):
        super(ModelCacheMixin, self)._blank_copy(c)
        c._models = set()
        c._exhausted = False
        c._eval_exhausted = weakref.WeakSet()
        c._max_exhausted = weakref.WeakSet()
        c._min_exhausted = weakref.WeakSet()

    def _copy(self, c):
        super(ModelCacheMixin, self)._copy(c)
        c._models = set(self._models)
        c._exhausted = self._exhausted
        c._eval_exhausted = weakref.WeakSet(self._eval_exhausted)
        c._max_exhausted = weakref.WeakSet(self._max_exhausted)
        c._min_exhausted = weakref.WeakSet(self._min_exhausted)

    def _ana_getstate(self):
        return (
            self._models,
            self._exhausted,
            tuple(self._eval_exhausted),
            tuple(self._max_exhausted),
            tuple(self._min_exhausted),
            super(ModelCacheMixin, self)._ana_getstate()
        )

    def _ana_setstate(self, s):
        (
            self._models,
            self._exhausted,
            _eval_exhausted,
            _max_exhausted,
            _min_exhausted,
            base_state
        ) = s
        super(ModelCacheMixin, self)._ana_setstate(base_state)
        self._eval_exhausted = weakref.WeakSet(_eval_exhausted)
        self._max_exhausted = weakref.WeakSet(_max_exhausted)
        self._min_exhausted = weakref.WeakSet(_min_exhausted)

    #
    # Model cleaning
    #

    def simplify(self, *args, **kwargs):
        results = super(ModelCacheMixin, self).simplify(*args, **kwargs)
        if len(results) > 0 and any(c is false for c in results):
            self._models.clear()
        return results

    def add(self, constraints, invalidate_cache=True, **kwargs):
        if len(constraints) == 0:
            return constraints

        old_vars = frozenset(self.variables)
        added = super(ModelCacheMixin, self).add(constraints, **kwargs)
        if len(added) == 0:
            return added

        new_vars = any(a.variables - old_vars for a in added)
        if new_vars or invalidate_cache:
            # shortcut for unsat
            if any(c is false for c in constraints):
                self._models.clear()

            still_valid = set(self._get_models(extra_constraints=added))
            if len(still_valid) != len(self._models):
                self._exhausted = False
                self._eval_exhausted.clear()
                self._max_exhausted.clear()
                self._min_exhausted.clear()
                self._models = still_valid

        return added

    def split(self):
        results = super(ModelCacheMixin, self).split()
        for r in results:
            r._models = { m.filter(r.variables) for m in self._models }
        return results

    def combine(self, others):
        combined = super(ModelCacheMixin, self).combine(others)

        if any(len(o._models) == 0 for o in others) or len(self._models) == 0:
            # this would need a solve anyways, so screw it
            return combined

        vars_count = len(self.variables) + sum(len(s.variables) for s in others)
        all_vars = self.variables.union(*[s.variables for s in others])
        if vars_count != len(all_vars):
            # this is the case where there are variables missing from the models.
            # We'll need more intelligence here to handle it
            return combined

        model_lists = [ self._models ]
        model_lists.extend(o._models for o in others)
        combined._models.update(
            ModelCache.combine(*product) for product in
            itertools.islice(itertools.product(*model_lists), self._MODEL_LIMIT)
        )
        return combined

    def update(self, other):
        """
        Updates this cache mixin with results discovered by the other split off one.
        """

        acceptable_models = [ m for m in other._models if set(m.model.keys()) == self.variables ]
        self._models.update(acceptable_models)
        self._eval_exhausted.update(other._eval_exhausted)
        self._max_exhausted.update(other._max_exhausted)
        self._min_exhausted.update(other._min_exhausted)

    #
    # Cache retrieval
    #

    def _model_hook(self, m):
        if len(self._models) < self._MODEL_LIMIT:
            self._models.add(ModelCache(m))

    def _get_models(self, extra_constraints=()):
        for m in self._models:
            if m.eval_constraints(extra_constraints):
                yield m

    def _get_batch_solutions(self, asts, n=None, extra_constraints=()):
        results = set()

        for m in self._get_models(extra_constraints):
            results.add(m.eval_list(asts))
            if len(results) == n:
                break

        return results

    def _get_solutions(self, e, n=None, extra_constraints=()):
        return tuple(v[0] for v in self._get_batch_solutions(
            [e], n=n, extra_constraints=extra_constraints
        ))


    #
    # Cached functions
    #


    def satisfiable(self, extra_constraints=(), **kwargs):
        for _ in self._get_models(extra_constraints=extra_constraints):
            return True
        return super(ModelCacheMixin, self).satisfiable(extra_constraints=extra_constraints, **kwargs)

    def batch_eval(self, asts, n, extra_constraints=(), **kwargs):
        results = self._get_batch_solutions(asts, n=n, extra_constraints=extra_constraints)

        if len(results) == n or (len(asts) == 1 and asts[0].cache_key in self._eval_exhausted):
            return results

        remaining = n - len(results)

        # TODO: faster to concat?
        if len(results) != 0:
            constraints = (all_operations.And(*[
                all_operations.Or(*[a!=v for a,v in zip(asts, r)]) for r in results
            ]),) + extra_constraints
        else:
            constraints = extra_constraints

        try:
            results.update(super(ModelCacheMixin, self).batch_eval(
                asts, remaining, extra_constraints=constraints, **kwargs
            ))
        except UnsatError:
            if len(results) == 0:
                raise

        if len(extra_constraints) == 0 and len(results) < n:
            self._eval_exhausted.update(e.cache_key for e in asts)

        return results

    def eval(self, e, n, **kwargs):
        return tuple( r[0] for r in ModelCacheMixin.batch_eval(self, [e], n=n, **kwargs) )

    def min(self, e, extra_constraints=(), **kwargs):
        cached = self._get_solutions(e, extra_constraints=extra_constraints)
        if len(cached) > 0 and (e.cache_key in self._eval_exhausted or e.cache_key in self._min_exhausted):
            return min(cached)
        else:
            m = super(ModelCacheMixin, self).min(e, extra_constraints=extra_constraints, **kwargs)
            self._min_exhausted.add(e.cache_key)
            return m

    def max(self, e, extra_constraints=(), **kwargs):
        cached = self._get_solutions(e, extra_constraints=extra_constraints)
        if len(cached) > 0 and (e.cache_key in self._eval_exhausted or e.cache_key in self._max_exhausted):
            return max(cached)
        else:
            m = super(ModelCacheMixin, self).max(e, extra_constraints=extra_constraints, **kwargs)
            self._max_exhausted.add(e.cache_key)
            return m

    def solution(self, e, v, extra_constraints=(), **kwargs):
        if isinstance(v, Base):
            cached = self._get_batch_solutions([e,v], extra_constraints=extra_constraints)
            if (e,v) in map(tuple, cached):
                return True
        else:
            cached = self._get_solutions(e, extra_constraints=extra_constraints)
            if v in cached:
                return True

        return super(ModelCacheMixin, self).solution(e, v, extra_constraints=extra_constraints, **kwargs)


from .. import backends, false
from ..errors import UnsatError
from ..ast import all_operations, Base
