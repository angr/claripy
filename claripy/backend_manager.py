class BackendManager(object):
    def __init__(self):
        self._eager_backends = [ ]
        self._accurate_backends = [ ]
        self._all_backends = [ ]
        self._backends_by_type = { }
        self._backends_by_name = { }

    def _register_backend(self, b, name, eager, accurate):
        self._backends_by_name[name] = b
        self._backends_by_type[b.__class__.__name__] = b
        self._all_backends.append(b)
        if eager:
            self._eager_backends.append(b)

        if accurate:
            self._accurate_backends.append(b)

    def __getattr__(self, a):
        if a in self._backends_by_name:
            return self._backends_by_name[a]
        else:
            raise AttributeError(a)

    def downsize(self):
        for b in self._all_backends:
            b.downsize()

backends = BackendManager()
