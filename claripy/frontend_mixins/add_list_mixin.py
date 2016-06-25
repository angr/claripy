class AddListMixin(object):
    def add(self, constraints, **kwargs):
        constraints = [ constraints ] if not isinstance(constraints, (list, tuple, set)) else constraints

        if len(constraints) == 0:
            return [ ]

        return super(AddListMixin, self).add(constraints, **kwargs)
