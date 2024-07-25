# pylint: disable=F0401,W0401,W0603,

__version__ = "9.2.113.dev0"

if bytes is str:
    raise Exception("This module is designed for python 3 only. Please install an older version to use python 2.")

import logging

l = logging.getLogger("claripy")
l.addHandler(logging.NullHandler())

from .errors import *
from . import operations as operations
from . import ops as _all_operations

from .backend_object import BackendObject

#
# backend objects
#

from . import bv as bv
from . import fp as fp
from . import vsa as vsa
from .fp import FSORT_DOUBLE as FSORT_DOUBLE, FSORT_FLOAT as FSORT_FLOAT
from .annotation import *

#
# Operations
#

from .ast.base import *
from .ast.bv import *
from .ast.fp import *
from .ast.bool import *
from .ast.strings import *
from . import ast


def BV(name, size, explicit_name=None):  # pylint:disable=function-redefined
    l.critical(
        "DEPRECATION WARNING: claripy.BV is deprecated and will soon be removed. Please use claripy.BVS, instead."
    )
    print("DEPRECATION WARNING: claripy.BV is deprecated and will soon be removed. Please use claripy.BVS, instead.")
    return BVS(name, size, explicit_name=explicit_name)


#
# Initialize the backends
#

from . import backends


def downsize():
    """
    Clear all temporary data associated with any backend
    """
    backends.downsize()


from . import simplifications


#
# Frontends
#

from .frontend import Frontend as _Frontend
from . import frontends as frontends
from . import frontend_mixins as frontend_mixins
from .solvers import *

#
# Convenient button
#


def reset():
    """
    Attempt to refresh any caching state associated with the module
    """
    downsize()
    from .ast import bv  # pylint:disable=redefined-outer-name

    bv._bvv_cache.clear()


from .debug import set_debug
