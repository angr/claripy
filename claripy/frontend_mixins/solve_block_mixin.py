class SolveBlockMixin:
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.can_solve = True

    def _blank_copy(self, c):
        super()._blank_copy(c)
        c.can_solve = True

    def _copy(self, c):
        super()._copy(c)
        c.can_solve = self.can_solve

    def __getstate__(self):
        return self.can_solve, super().__getstate__()

    def __setstate__(self, s):
        self.can_solve, base_state = s
        super().__setstate__(base_state)

    def eval(self, *args, **kwargs):
        assert self.can_solve
        return super().eval(*args, **kwargs)

    def batch_eval(self, *args, **kwargs):
        assert self.can_solve
        return super().batch_eval(*args, **kwargs)

    def min(self, *args, **kwargs):
        assert self.can_solve
        return super().min(*args, **kwargs)

    def max(self, *args, **kwargs):
        assert self.can_solve
        return super().max(*args, **kwargs)

    def satisfiable(self, *args, **kwargs):
        assert self.can_solve
        return super().satisfiable(*args, **kwargs)

    def solution(self, *args, **kwargs):
        assert self.can_solve
        return super().solution(*args, **kwargs)
