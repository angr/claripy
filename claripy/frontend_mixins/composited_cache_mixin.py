#hits = 0
#misses = 0
#ejects = 0

class CompositedCacheMixin:
    def __init__(self, *args, **kwargs):
        super(CompositedCacheMixin, self).__init__(*args, **kwargs)
        self._merged_solvers = { }

    def _blank_copy(self, c):
        super(CompositedCacheMixin, self)._blank_copy(c)
        c._merged_solvers = { }

    def _copy(self, c):
        super(CompositedCacheMixin, self)._copy(c)
        c._merged_solvers = dict(self._merged_solvers)

    def __setstate__(self, base_state):
        super().__setstate__(base_state)
        self._merged_solvers = { }

    #
    # Cache stuff
    #

    def _remove_cached(self, names):
        #global ejects

        for k in list(self._merged_solvers.keys()):
            if k & names:
                #ejects += 1
                self._merged_solvers.pop(k)

    def _solver_for_names(self, names):
        #global hits, misses

        n = frozenset(names)
        try:
            r = self._merged_solvers[frozenset(n)]
            #hits += 1
            return r
        except KeyError:
            #misses += 1
            s = super(CompositedCacheMixin, self)._solver_for_names(names)
            self._merged_solvers[n] = s
            return s

    def downsize(self):
        super(CompositedCacheMixin, self).downsize()
        self._merged_solvers = { }

    def _store_child(self, s, **kwargs):
        self._remove_cached(s.variables)
        return super(CompositedCacheMixin, self)._store_child(s, **kwargs)
