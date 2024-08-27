from __future__ import annotations

import logging

l = logging.getLogger("claripy.ops")

#
# AST creation
#


def AbstractLocation(*args, **kwargs):  # pylint:disable=no-self-use
    return vsa.AbstractLocation(*args, **kwargs)


#
# Some operations
#


#
# sigh
#

# pylint:disable=wildcard-import,unused-wildcard-import,wrong-import-position
from . import vsa
from .ast.base import *
from .ast.bool import *
from .ast.bv import *
from .ast.fp import *
from .ast.strings import *

VS = ValueSet
