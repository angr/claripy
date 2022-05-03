from .setup_clari import Setup, clari

import logging
import os

# Configure claricpp
s = Setup(debug_mode="CLARICPP_DEBUG" in os.environ)
s.establish_link(logger=logging.getLogger("Claricpp"))
s.config(src_root=os.path.join(os.path.dirname(__file__), "cpp_src"))
s.define_members(legacy_support=True)

# Exports
__all__ = ("clari",)
