from __future__ import annotations

from .backend_vsa import BackendVSA
from .bool_result import BoolResult, FalseResult, MaybeResult, TrueResult
from .discrete_strided_interval_set import DEFAULT_MAX_CARDINALITY_WITHOUT_COLLAPSING, DiscreteStridedIntervalSet
from .strided_interval import CreateStridedInterval, StridedInterval
from .valueset import ValueSet

__all__ = (
    "BackendVSA",
    "BoolResult",
    "FalseResult",
    "MaybeResult",
    "TrueResult",
    "DEFAULT_MAX_CARDINALITY_WITHOUT_COLLAPSING",
    "DiscreteStridedIntervalSet",
    "CreateStridedInterval",
    "StridedInterval",
    "ValueSet",
)
