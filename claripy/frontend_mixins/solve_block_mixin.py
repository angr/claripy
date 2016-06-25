class SolveBlockMixin(object):
    def __init__(self, *args, **kwargs):
        super(SolveBlockMixin, self).__init__(*args, **kwargs)
        self.can_solve = True

    def _blank_copy(self, c):
        super(SolveBlockMixin, self)._blank_copy(c)
        c.can_solve = True

    def _copy(self, c):
        super(SolveBlockMixin, self)._copy(c)
        c.can_solve = self.can_solve

    def eval(self, *args, **kwargs):
        assert self.can_solve
        return super(SolveBlockMixin, self).eval(*args, **kwargs)

    def batch_eval(self, *args, **kwargs):
        assert self.can_solve
        return super(SolveBlockMixin, self).batch_eval(*args, **kwargs)

    def min(self, *args, **kwargs):
        assert self.can_solve
        return super(SolveBlockMixin, self).min(*args, **kwargs)

    def max(self, *args, **kwargs):
        assert self.can_solve
        return super(SolveBlockMixin, self).max(*args, **kwargs)

    def satisfiable(self, *args, **kwargs):
        assert self.can_solve
        return super(SolveBlockMixin, self).satisfiable(*args, **kwargs)

    def solution(self, *args, **kwargs):
        assert self.can_solve
        return super(SolveBlockMixin, self).solution(*args, **kwargs)
