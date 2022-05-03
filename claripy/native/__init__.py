from .setup_clari import Setup, clari

import logging
import os

# Configure claricpp
s = Setup(debug_mode="CLARICPP_DEBUG" in os.environ)
s.link(logger=logging.getLogger("Claricpp"))
s.define_members(legacy_support=True)

# Exports
__all__ = ("clari",)
