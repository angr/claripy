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


def create(base: type, op: str, py_args: List[Any], length: Optional[int]) -> Tuple[Type["clari.Expr.Base"], LegacyData]:
    """
    Create a claricpp object with op type op and py_args as arguments
    Length is passed if the object is sized
    Note: This expects claripy ops in py_args define both ._native
    and ._legacy using values gotten from calling this method
    :param base: The base claripy AST type (used for checking of .args[i] is a claripy AST)
    :param op: The claripy op
    :param py_args: The op arguments
    :param length: The length argument passed to claripy.ast.base's __init__ function
    :return: The native op & a data object needed for legacy support
    """
    return _create(base, op, py_args, length)


__all__ = ("create", "args",)