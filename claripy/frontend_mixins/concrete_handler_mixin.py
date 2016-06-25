class ConcreteHandlerMixin(object):
    def eval(self, e, n, **kwargs): #pylint:disable=unused-argument
        c = self._concrete_value(e)
        if c is not None:
            return (c,)
        else:
            return super(ConcreteHandlerMixin, self).eval(e, n, **kwargs)

    def batch_eval(self, exprs, n, **kwargs): #pylint:disable=unused-argument
        concrete_exprs = [ self._concrete_value(e) for e in exprs ]
        symbolic_exprs = [ e for e,c in zip(exprs, concrete_exprs) if c is None ]

        if len(symbolic_exprs) == 0:
            return [ concrete_exprs ]

        symbolic_results = map(
            list,
            super(ConcreteHandlerMixin, self).batch_eval(symbolic_exprs, n, **kwargs)
        )
        return [
            tuple((c if c is not None else r.pop(0)) for c in concrete_exprs)
            for r in symbolic_results
        ]

    def max(self, e, **kwargs):
        c = self._concrete_value(e)
        if c is not None:
            return c
        else:
            return super(ConcreteHandlerMixin, self).max(e, **kwargs)

    def min(self, e, **kwargs):
        c = self._concrete_value(e)
        if c is not None:
            return c
        else:
            return super(ConcreteHandlerMixin, self).min(e, **kwargs)

    def solution(self, e, v, **kwargs):
        ce = self._concrete_value(e)
        cv = self._concrete_value(v)

        if ce is None or cv is None:
            return super(ConcreteHandlerMixin, self).solution(e, v, **kwargs)
        else:
            return ce == cv

    def is_true(self, e, **kwargs):
        c = self._concrete_value(e)
        if c is not None:
            return c
        else:
            return super(ConcreteHandlerMixin, self).is_true(e, **kwargs)

    def is_false(self, e, **kwargs):
        c = self._concrete_value(e)
        if c is not None:
            return not c
        else:
            return super(ConcreteHandlerMixin, self).is_false(e, **kwargs)
