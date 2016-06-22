import weakref
import itertools

class ModelCacheMixin(object):
    def __init__(self, *args, **kwargs):
        super(ModelCacheMixin, self).__init__(*args, **kwargs)
        self._models = [ ]
        self._model_replacements = [ ]
        self._exhausted = False
        self._eval_exhausted = weakref.WeakKeyDictionary()
        self._max_exhausted = weakref.WeakKeyDictionary()
        self._min_exhausted = weakref.WeakKeyDictionary()

    def _blank_copy(self, c):
        super(ModelCacheMixin, self)._blank_copy(c)
        c._models = [ ]
        c._model_replacements = [ ]
        c._exhausted = False
        c._eval_exhausted = weakref.WeakKeyDictionary()
        c._max_exhausted = weakref.WeakKeyDictionary()
        c._min_exhausted = weakref.WeakKeyDictionary()

    def _copy(self, c):
        super(ModelCacheMixin, self)._copy(c)
        c._models = list(self._models)
        c._model_replacements = list(self._model_replacements)
        c._exhausted = self._exhausted
        c._eval_exhausted = weakref.WeakKeyDictionary(self._eval_exhausted)
        c._max_exhausted = weakref.WeakKeyDictionary(self._max_exhausted)
        c._min_exhausted = weakref.WeakKeyDictionary(self._min_exhausted)

    def _ana_getstate(self):
        return (
            self._models,
            self._exhausted,
            self._eval_exhausted.keys(),
            self._max_exhausted.keys(),
            self._min_exhausted.keys(),
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
        self._model_replacements = [ weakref.WeakKeyDictionary() for _ in self._models ]
        self._eval_exhausted = weakref.WeakKeyDictionary((k,True) for k in _eval_exhausted)
        self._max_exhausted = weakref.WeakKeyDictionary((k,True) for k in _max_exhausted)
        self._min_exhausted = weakref.WeakKeyDictionary((k,True) for k in _min_exhausted)

    #
    # Model cleaning
    #

    def add(self, constraints, invalidate_cache=True, **kwargs):
        if len(constraints) == 0:
            return constraints

        added = super(ModelCacheMixin, self).add(constraints, **kwargs)

        if any(a.variables - self.variables for a in added) or invalidate_cache:
            still_valid = [ (m,r) for m,r in self._get_models(extra_constraints=added) ]
            if len(still_valid) == 0:
                self._models = [ ]
                self._model_replacements = [ ]
            else:
                self._models, self._model_replacements = map(list, zip(*still_valid))
        return added

    def split(self):
        results = super(ModelCacheMixin, self).split()
        for r in results:
            r._models = [
                { k:v for k,v in m.iteritems() if k in r.variables }
                for m in self._models
            ]
            r._model_replacements = [ weakref.WeakKeyDictionary() for _ in r._models ]
        return results

    def combine(self, others):
        combined = super(ModelCacheMixin, self).combine(others)

        if any(len(o._models) == 0 for o in others) or len(self._models) == 0:
            # this would need a solve anyways, so screw it
            return combined

        models = [ self._models ]
        models.extend(o._models for o in others)

        new_models = [ ]
        for product in itertools.product(*models):
            combined_model = { }

            conflict = False
            missing = set()
            for m,s in zip(product, itertools.chain([self], others)):
                for v in s.variables:
                    if (v in combined_model and combined_model[v] != m[v]) or v in missing:
                        conflict = True
                    if v not in m:
                        missing.add(v)
                    else:
                        combined_model[v] = m[v]

            if not conflict:
                new_models.append(combined_model)

        combined._models = new_models
        combined._model_replacements = [ weakref.WeakKeyDictionary() for _ in self._models ]
        return combined

    #
    # Model-driven evaluation
    #

    @staticmethod
    def _eval_ast(ast, model, replacements):
        new_ast = ast._replace(
            replacements,
            leaf_operation=lambda a: (
                all_operations.BVV(model.get(a.args[0], 0), a.length) if a.op == 'BVS' else
                all_operations.BoolV(model.get(a.args[0], true)) if a.op == 'BoolS' else
                all_operations.FPV(model.get(a.args[0], 0.0), a.args[1]) if a.op == 'FPS' else
                a
            )
        )
        return backends.concrete.eval(new_ast, 1)[0]

    @staticmethod
    def _eval_constraints(constraints, model, replacements):
        return all(ModelCacheMixin._eval_ast(c, model, replacements) for c in constraints)

    @staticmethod
    def _eval_list(asts, model, replacements):
        return tuple( ModelCacheMixin._eval_ast(c, model, replacements) for c in asts )

    #
    # Cache retrieval
    #

    def _model_hook(self, m):
        self._models.append(m)
        self._model_replacements.append(weakref.WeakKeyDictionary())

    def _get_models(self, extra_constraints=(), n=None):
        mr = zip(self._models, self._model_replacements)
        if len(extra_constraints) == 0:
            return mr[:n] if n is not None else mr
        else:
            return [ (m,r) for m,r in mr if self._eval_constraints(extra_constraints, m, r) ]

    def _get_batch_solutions(self, asts, n=None, extra_constraints=()):
        results = set()

        for m,r in self._get_models(extra_constraints):
            results.add(self._eval_list(asts, m, r))
            if len(results) == n:
                break

        return results

    def _get_solutions(self, e, n=None, extra_constraints=()):
        return tuple(v[0] for v in self._get_batch_solutions([e], n=n, extra_constraints=extra_constraints))


    #
    # Cached functions
    #


    def satisfiable(self, extra_constraints=(), **kwargs):
        for _ in self._get_models(extra_constraints=extra_constraints, n=1):
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
            self._eval_exhausted.update({e.cache_key:True for e in asts})

        return results

    def eval(self, e, n, **kwargs):
        return tuple( r[0] for r in ModelCacheMixin.batch_eval(self, [e], n=n, **kwargs) )

    def min(self, e, extra_constraints=(), **kwargs):
        cached = self._get_solutions(e, extra_constraints=extra_constraints)
        if len(cached) > 0 and (e.cache_key in self._eval_exhausted or e.cache_key in self._min_exhausted):
            return min(cached)
        else:
            m = super(ModelCacheMixin, self).min(e, extra_constraints=extra_constraints, **kwargs)
            self._min_exhausted[e.cache_key] = True
            return m

    def max(self, e, extra_constraints=(), **kwargs):
        cached = self._get_solutions(e, extra_constraints=extra_constraints)
        if len(cached) > 0 and (e.cache_key in self._eval_exhausted or e.cache_key in self._max_exhausted):
            return max(cached)
        else:
            m = super(ModelCacheMixin, self).max(e, extra_constraints=extra_constraints, **kwargs)
            self._max_exhausted[e.cache_key] = True
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


from .. import backends
from ..errors import UnsatError
from ..ast import all_operations, Base
from .. import true
