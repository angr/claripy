from __future__ import annotations

from itertools import product
from typing import TYPE_CHECKING

from claripy.ast.bool import Bool, false, true

if TYPE_CHECKING:
    from claripy.ast.base import Base


def _is_leaf(ast: Base) -> bool:
    return not isinstance(ast, Bool) or ast.op not in {"Not", "And", "Or"}


def linearize_parent_first(ast: Base) -> list[Base]:
    """Takes an AST and returns a list of all the nodes in the AST, in
    parent-first order."""
    results = [ast]

    if _is_leaf(ast):
        return results

    for child in ast.args:
        results.extend(linearize_parent_first(child))

    return results


def simplify_boolean_expr(ast: Bool) -> Bool:
    """Simplifies a boolean expression AST.

    Supports BoolS/BoolV, Not, And, Or. For this simplification, "simple" means
    fewest nodes in the AST.
    """
    match ast.op:
        case "Not":
            child = simplify_boolean_expr(ast.args[0])

            # Constant elimination
            if child.identical(true):
                return false
            if child.identical(false):
                return true

            # Double negation elimination
            if child.op == "Not":
                return child.args[0]

            return ~child

        case "And":
            left = simplify_boolean_expr(ast.args[0])
            right = simplify_boolean_expr(ast.args[1])

            # Idempotent elimination
            # x & false = false, false & x = false
            if left.identical(false) or right.identical(false):
                return false

            # Constant elimination
            # true & x = x
            if left.identical(right, strict=True):
                return left
            # x & true = x
            if left.identical(true):
                return right

            # Indempotent elimination
            # x & x = x
            if right.identical(true):
                return left

            # Xor elimination
            # !x & x = false
            if left.op == "Not" and right.identical(left.args[0], strict=True):
                return false
            # x & !x = false
            if right.op == "Not" and left.identical(right.args[0], strict=True):
                return false

            # Absorption
            # (x | y) & x = x
            if left.op == "Or" and (right.identical(left.args[0], strict=True) or right.identical(left.args[1])):
                return right
            # x & (x | y) = x
            if right.op == "Or" and (left.identical(right.args[0], strict=True) or left.identical(right.args[1])):
                return left

            # Distributive
            # (x | y) & (x | z) = x | (y & z)
            if left.op == right.op == "Or":
                for li, ri in product([0, 1], [0, 1]):
                    if left.args[li].identical(right.args[ri], strict=True):
                        return left.args[li] | (left.args[0 if li else 1] & right.args[0 if ri else 1])

            return left & right

        case "Or":
            left = simplify_boolean_expr(ast.args[0])
            right = simplify_boolean_expr(ast.args[1])

            # Idempotent elimination
            # x | false = false, false | x = false
            if left.identical(true) or right.identical(true):
                return true

            # Indempotent elimination
            # x | x = x
            if left.identical(right, strict=True):
                return left

            # Constant elimination
            # false | x = x
            if left.identical(false):
                return right
            # x | false = x
            if right.identical(false):
                return left

            # Xor elimination
            # !x & x = true
            if left.op == "Not" and right.identical(left.args[0], strict=True):
                return true
            # x & !x = true
            if right.op == "Not" and left.identical(right.args[0], strict=True):
                return true

            # Absorption
            # (x & y) | x = x
            if left.op == "And" and (
                right.identical(left.args[0], strict=True) or right.identical(left.args[1], strict=True)
            ):
                return right
            # x | (x & y) = x
            if right.op == "And" and (left.identical(right.args[0]) or left.identical(right.args[1], strict=True)):
                return left

            # Distributive
            # (x & y) | (x & z) = x & (y | z)
            if left.op == right.op == "And":
                for li, ri in product([0, 1], [0, 1]):
                    if left.args[li].identical(right.args[ri], strict=True):
                        return left.args[li] & (left.args[0 if li else 1] | right.args[0 if ri else 1])

            return left | right

        case _:
            return ast
