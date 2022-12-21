class ConstraintDeduplicatorMixin:
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._constraint_hashes = set()

    def _blank_copy(self, c):
        super()._blank_copy(c)
        c._constraint_hashes = set()

    def _copy(self, c):
        super()._copy(c)
        c._constraint_hashes = set(self._constraint_hashes)

    def __getstate__(self):
        return self._constraint_hashes, super().__getstate__()

    def __setstate__(self, s):
        self._constraint_hashes, base_state = s
        super().__setstate__(base_state)

    def simplify(self, **kwargs):
        added = super().simplify(**kwargs)
        # we only add to the constraint hashes because we want to
        # prevent previous (now simplified) constraints from
        # being re-added
        self._constraint_hashes.update(map(hash, added))
        return added

    def add(self, constraints, **kwargs):
        filtered = tuple(c for c in constraints if hash(c) not in self._constraint_hashes)
        if len(filtered) == 0:
            return filtered

        added = super().add(filtered, **kwargs)
        self._constraint_hashes.update(map(hash, added))
        return added
