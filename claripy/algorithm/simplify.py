from __future__ import annotations

import logging
from itertools import chain
from typing import TypeVar

from claripy.ast.base import Base, SimplificationLevel

log = logging.getLogger(__name__)

T = TypeVar("T", bound=Base)


def simplify(expr: T) -> T:
    """
    Simplify an expression.
    """

    if expr.is_leaf() or expr._simplified == SimplificationLevel.FULL_SIMPLIFY:
        return expr

    simplified = expr._first_backend("simplify")
    if simplified is None:
        log.debug("Unable to simplify expression")
        return expr

    # Copy some parameters (that should really go to the Annotation backend)
    simplified._uninitialized = expr.uninitialized

    # dealing with annotations
    if expr.annotations:
        ast_args = tuple(a for a in expr.args if isinstance(a, Base))
        annotations = tuple(
            set(
                chain(
                    chain.from_iterable(a._relocatable_annotations for a in ast_args),
                    tuple(a for a in expr.annotations),
                )
            )
        )
        if annotations != simplified.annotations:
            simplified = simplified.remove_annotations(simplified.annotations)
            simplified = simplified.annotate(*annotations)

    return simplified
