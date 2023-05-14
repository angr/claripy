from __future__ import annotations
from typing import TYPE_CHECKING, Union

if TYPE_CHECKING:
    from claripy.backends.backend_concrete import BackendConcrete
    from claripy.backends.backend_smtlib import BackendSMTLibBase
    from claripy.backends.backend_smtlib_solvers.cvc4_popen import SolverBackendCVC4
    from claripy.backends.backend_vsa import BackendVSA
    from claripy.backends.backend_z3 import BackendZ3


class BackendManager:
    def __init__(self):
        self._eager_backends = []
        self._quick_backends = []
        self._all_backends = []
        self._backends_by_type = {}
        self._backends_by_name = {}

    def _register_backend(self, b: BackendSMTLibBase, name: str, eager: bool, quick: bool) -> None:
        self._backends_by_name[name] = b
        self._backends_by_type[b.__class__.__name__] = b
        self._all_backends.append(b)
        if eager:
            self._eager_backends.append(b)

        if quick:
            self._quick_backends.append(b)

    def __getattr__(self, a: str) -> BackendVSA | BackendSMTLibBase | BackendConcrete | BackendZ3 | SolverBackendCVC4:
        if a in self._backends_by_name:
            return self._backends_by_name[a]
        else:
            raise AttributeError(a)

    def downsize(self):
        for b in self._all_backends:
            b.downsize()


backends = BackendManager()
