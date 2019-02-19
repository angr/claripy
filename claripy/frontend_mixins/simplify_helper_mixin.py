class SimplifyHelperMixin:
    def max(self, *args, **kwargs):
        self.simplify()
        return super(SimplifyHelperMixin, self).max(*args, **kwargs)

    def min(self, *args, **kwargs):
        self.simplify()
        return super(SimplifyHelperMixin, self).min(*args, **kwargs)

    def eval(self, e, n, *args, **kwargs):
        if n > 1:
            self.simplify()
        return super(SimplifyHelperMixin, self).eval(e, n, *args, **kwargs)

    def batch_eval(self, e, n, *args, **kwargs):
        if n > 1:
            self.simplify()
        return super(SimplifyHelperMixin, self).batch_eval(e, n, *args, **kwargs)
