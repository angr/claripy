from typing import Optional, Tuple, List, Dict, Any
from dataclasses import dataclass

@dataclass(frozen=True, kw_only=True, eq=False, match_args=False, slots=True)
class LegacyData:
    """
    Additional data needed to construct .args from a claricpp object
    Ex. claripy shoves extra info into BVSs when doing VS stuff due to hacks
    """
    py_args: Tuple[Any] ## TODO: delete after testing only needed to verify .args works
    exprs: Optional[Dict[int, "claripy.expr.Base"]] = None
    bvs: Optional[List] = None
