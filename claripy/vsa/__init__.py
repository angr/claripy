from __future__ import annotations

from .bool_result import BoolResult, FalseResult, MaybeResult, TrueResult
from .discrete_strided_interval_set import DEFAULT_MAX_CARDINALITY_WITHOUT_COLLAPSING, DiscreteStridedIntervalSet
from .strided_interval import CreateStridedInterval, StridedInterval
from .valueset import ValueSet

__all__ = (
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
