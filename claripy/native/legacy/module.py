"""
This file represents a python module which should be installed as clari.Legacy
"""
from typing import List, Optional, Any, Tuple, Type

from .args import args as _args
from .create import create as _create
from .data_types import LegacyData


def args(ast: "ClaripyBase") -> List[Any]:
    """
    Return the legacy .args for the claripy expr
    Note: This assumes ast.op and ast._uninitialized are defined
    """
    return _args(ast.op, ast._uninitialized, ast._native, ast._legacy)


def create(*args, **kwargs) -> Tuple[Type["clari.Expr.Base"], LegacyData]:
    return _create(*args, **kwargs)
create.__doc__ = _create.__doc__


__all__ = ("create", "args")