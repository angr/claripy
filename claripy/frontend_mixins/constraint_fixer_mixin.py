from typing import TYPE_CHECKING, Union

from claripy import BoolV

if TYPE_CHECKING:
    from claripy.ast.bool import Bool


class ConstraintFixerMixin:
    def add(self, constraints: Union["Bool", list["Bool"], set["Bool"], tuple["Bool", ...]], **kwargs) -> list["Bool"]:
        constraints = [constraints] if not isinstance(constraints, list | tuple | set) else constraints

        if len(constraints) == 0:
            return []

        constraints = [BoolV(c) if isinstance(c, bool) else c for c in constraints]
        return super().add(constraints, **kwargs)
