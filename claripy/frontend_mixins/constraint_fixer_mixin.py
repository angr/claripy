from typing import TYPE_CHECKING, List, Union, Set, Tuple

if TYPE_CHECKING:
    from claripy.ast.bool import Bool


class ConstraintFixerMixin:
    def add(self, constraints: Union["Bool", List["Bool"], Set["Bool"], Tuple["Bool", ...]], **kwargs) -> List["Bool"]:
        constraints = [constraints] if not isinstance(constraints, (list, tuple, set)) else constraints

        if len(constraints) == 0:
            return []

        constraints = [BoolV(c) if isinstance(c, bool) else c for c in constraints]
        return super().add(constraints, **kwargs)


from .. import BoolV
