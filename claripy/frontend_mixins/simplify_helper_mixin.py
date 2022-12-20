class SimplifyHelperMixin:
    def max(self, *args, **kwargs):
        self.simplify()
        return super().max(*args, **kwargs)

    def min(self, *args, **kwargs):
        self.simplify()
        return super().min(*args, **kwargs)

    def eval(self, e, n, *args, **kwargs):
        if n > 1:
            self.simplify()
        return super().eval(e, n, *args, **kwargs)

    def batch_eval(self, e, n, *args, **kwargs):
        if n > 1:
            self.simplify()
        return super().batch_eval(e, n, *args, **kwargs)
