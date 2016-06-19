class ConstraintDeduplicatorMixin(object):
    def __init__(self, *args, **kwargs):
        super(ConstraintDeduplicatorMixin, self).__init__(*args, **kwargs)
        self._constraint_hashes = set()

    def _blank_copy(self, c):
        super(ConstraintDeduplicatorMixin, self)._blank_copy(c)
        c._constraint_hashes = set()

    def _copy(self, c):
        super(ConstraintDeduplicatorMixin, self)._copy(c)
        c._constraint_hashes = set(self._constraint_hashes)

    #
    # Serialization
    #

    def _ana_getstate(self):
        return self._constraint_hashes, super(ConstraintDeduplicatorMixin, self)._ana_getstate()

    def _ana_setstate(self, s):
        self._constraint_hashes, base_state = s
        super(ConstraintDeduplicatorMixin, self)._ana_setstate(base_state)

    def simplify(self, **kwargs):
        added = super(ConstraintDeduplicatorMixin, self).simplify(**kwargs)
        # we only add to the constraint hashes because we want to
        # prevent previous (now simplified) constraints from
        # being re-added
        self._constraint_hashes.update(map(hash, added))
        return added

    def add(self, constraints, **kwargs):
        filtered = tuple(c for c in constraints if hash(c) not in self._constraint_hashes)
        if len(filtered) == 0:
            return filtered

        added = super(ConstraintDeduplicatorMixin, self).add(filtered, **kwargs)
        self._constraint_hashes.update(map(hash, added))
        return added
