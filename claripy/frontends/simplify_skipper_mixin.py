class SimplifySkipperMixin(object):
    def __init__(self, *args, **kwargs):
        super(SimplifySkipperMixin, self).__init__(*args, **kwargs)
        self._simplified = True

    def _blank_copy(self, c):
        super(SimplifySkipperMixin, self)._blank_copy(c)
        c._simplified = True

    def _copy(self, c):
        super(SimplifySkipperMixin, self)._copy(c)
        c._simplified = self._simplified

    def _ana_getstate(self):
        return self._simplified, super(SimplifySkipperMixin, self)._ana_getstate()

    def _ana_setstate(self, s):
        self._simplified, base_state = s
        super(SimplifySkipperMixin, self)._ana_setstate(base_state)

    #
    # Simplification skipping
    #

    def add(self, *args, **kwargs):
        added = super(SimplifySkipperMixin, self).add(*args, **kwargs)
        if len(added) > 0:
            self._simplified = False
        return added

    def simplify(self, *args, **kwargs):
        if self._simplified:
            return self.constraints
        else:
            self._simplified = True
            return super(SimplifySkipperMixin, self).simplify(*args, **kwargs)
