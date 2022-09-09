"""
Load claricpp with support for legacy functions such as .args
Warning: This requires hooking clari, it modifies the module
"""
from .load import Load

__all__ = ("Load", )