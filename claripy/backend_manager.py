from __future__ import annotations


class BackendManager:
    """BackendManager is a class that manages all backends in claripy. It is a singleton class."""

    def __init__(self):
        self._all_backends = []
        self._backends_by_type = {}
        self._backends_by_name = {}

    def _register_backend(self, b, name):
        self._backends_by_name[name] = b
        self._backends_by_type[b.__class__.__name__] = b
        self._all_backends.append(b)

    def __getattr__(self, a):
        if a in self._backends_by_name:
            return self._backends_by_name[a]
        raise AttributeError(a)

    def downsize(self):
        for b in self._all_backends:
            b.downsize()


backends = BackendManager()
