from __future__ import annotations


class BackendManager:
    def __init__(self):
        self._eager_backends = []
        self._quick_backends = []
        self._all_backends = []
        self._backends_by_type = {}
        self._backends_by_name = {}

    def _register_backend(self, b, name, eager, quick):
        self._backends_by_name[name] = b
        self._backends_by_type[b.__class__.__name__] = b
        self._all_backends.append(b)
        if eager:
            self._eager_backends.append(b)

        if quick:
            self._quick_backends.append(b)

    def __getattr__(self, a):
        if a in self._backends_by_name:
            return self._backends_by_name[a]
        else:
            raise AttributeError(a)

    def downsize(self):
        for b in self._all_backends:
            b.downsize()


backends = BackendManager()
