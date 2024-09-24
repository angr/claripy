from __future__ import annotations

from .backend import Backend
from .backend_concrete import BackendConcrete
from .backend_vsa import BackendVSA
from .backend_z3 import BackendZ3

concrete = BackendConcrete()
z3 = BackendZ3()
vsa = BackendVSA()

all_backends = [concrete, z3, vsa]
backends_by_type = {b.__class__.__name__: b for b in all_backends}

__all__ = (
    "Backend",
    "BackendZ3",
    "BackendConcrete",
    "BackendVSA",
    "all_backends",
    "backends_by_type",
    "concrete",
    "z3",
    "vsa",
)
