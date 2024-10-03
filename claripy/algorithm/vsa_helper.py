from __future__ import annotations

from typing import TYPE_CHECKING

import claripy

if TYPE_CHECKING:
    from claripy.ast import BV


def singlevalued(expr: BV) -> bool:
    """Determines if the expression is single-valued."""
    return claripy.backends.vsa.singlevalued(expr)


def multivalued(expr: BV) -> bool:
    """Determines if the expression is multi-valued."""
    return claripy.backends.vsa.multivalued(expr)


def cardinality(expr: BV) -> int:
    """Returns the number of possible values the expression can take."""
    return claripy.backends.vsa.cardinality(expr)


def stride(expr: BV) -> int:
    """Returns the stride of the expression."""
    return claripy.backends.vsa.stride(expr)


def constraint_to_si(expr: BV) -> tuple[bool, list[tuple[BV, BV]]]:
    """
    Convert a constraint to SI if possible.

    :param expr: The expression to convert.
    :return: A tuple of satisfiable and a list of replacements.
    """

    return claripy.backends.vsa.constraint_to_si(expr)
