from .backend_z3 import BackendZ3
from .backend_concrete import BackendConcrete
from .backend_vsa import BackendVSA

z3 = BackendZ3()
concrete = BackendConcrete()
vsa = BackendVSA()

_eager_backends = [concrete]
_quick_backends = [concrete]
_all_backends = [z3, concrete, vsa]
_backends_by_type = {
    z3.__class__.__name__: z3,
    concrete.__class__.__name__: concrete,
    vsa.__class__.__name__: vsa,
}

__all__ = [
    "BackendZ3",
    "BackendConcrete",
    "BackendVSA",
    "z3",
    "concrete",
    "vsa",
    "_eager_backends",
    "_quick_backends",
    "_all_backends",
    "_backends_by_type",
]
