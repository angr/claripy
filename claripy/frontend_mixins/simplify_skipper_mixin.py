class SimplifySkipperMixin:
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._simplified = True

    def _blank_copy(self, c):
        super()._blank_copy(c)
        c._simplified = True

    def _copy(self, c):
        super()._copy(c)
        c._simplified = self._simplified

    def __getstate__(self):
        return self._simplified, super().__getstate__()

    def __setstate__(self, s):
        self._simplified, base_state = s
        super().__setstate__(base_state)

    #
    # Simplification skipping
    #

    def add(self, *args, **kwargs):
        added = super().add(*args, **kwargs)
        if len(added) > 0:
            self._simplified = False
        return added

    def simplify(self, *args, **kwargs):
        if self._simplified:
            return self.constraints
        else:
            self._simplified = True
            return super().simplify(*args, **kwargs)
