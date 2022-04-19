from enum import Enum
import functools
import logging
import os

import clari

logging.basicConfig(
    level=logging.DEBUG,
    format="%(levelname)-7s | %(asctime)-23s | %(name)-8s | %(message)s",
)  # TODO: remove

# Config
log = logging.getLogger(__name__)
claricpp_debug = "CLARICPP_DEBUG" in os.environ


### Init Claricpp and Claripy link


def _init_logging():
    # Claricpp might be compiled without this option
    if hasattr(clari.API, "set_log_level"):
        # Hook setLevel to call the C++ version as well
        log._original_setLevel = log.setLevel

        def _set_level(lvl):
            log._original_setLevel(lvl)
            clari.API.set_log_level(lvl)

        log.setLevel = _set_level
        log.info("Synchrnoizing Claripy/Claricpp log levels: hooking log.setLevel")
    else:
        lvl = logging.getLevelName(clari.API.get_log_level())
        log.info("Claricpp's log level is fixed at: " + lvl)
    # Update log level (also synchronizes log levels if applicable)
    log.setLevel(logging.DEBUG if claricpp_debug else log.getEffectiveLevel())
    clari.API.install_logger(lambda a, b, c: logging.getLogger(a).log(b, c))


# Init logging; use function to scope variables
_init_logging()
del _init_logging  # Cleanup

# Init backtraces
clari.Util.Err.Claricpp.toggle_backtrace(claricpp_debug)
if claricpp_debug:
    clari.API.enable_signal_traces()
log.info("Native backtraces " + ("en" if claricpp_debug else "dis") + "abled")


### Setup Exception Translations


def _cls_init(self, *args, **kwargs):
    def native_trace():
        if not hasattr(self, "_native_trace"):
            lazy = self.__lazy_bt
            del self.__lazy_bt  # Free the lazy object since we cach the evaluation
            if lazy is not None:
                try:
                    lazy = lazy.str()  # Evaluate lazy
                except Exception as e:
                    log.error("Failed to extract native backtrace because: " + str(e))
            self._native_trace = lazy
        return self._native_trace

    self.__lazy_bt = clari.Util.Err.Claricpp.lazy_backtrace()  # should never throw
    # Set the native_trace
    self.native_trace = native_trace
    self.__original_init(*args, **kwargs)


# Override builtin init with our new init
clari.py_err._internal.Base.__original_init = clari.py_err._internal.Base.__init__
clari.py_err._internal.Base.__init__ = _cls_init
del _cls_init  # Cleanup


### Operators ###


# Fixes
# TODO: make this work for instance variables clari.Expr.Base.args = clari.Expr.Base.python_children

# Define repr
clari.Annotation.Base.__repr__ = clari.Annotation.Base.repr
clari.Annotation.Vec.__repr__ = clari.Annotation.Vec.repr
clari.Expr.Base.__repr__ = clari.Expr.Base.repr
clari.Op.Base.__repr__ = clari.Op.Base.repr

# Fix hashing
r_hash = lambda x: x.hash
clari.Annotation.Base.__hash__ = r_hash
clari.Annotation.Vec.__hash__ = r_hash
clari.Expr.Base.__hash__ = r_hash
clari.Op.Base.__hash__ = r_hash
del r_hash

# Equality
clari.Expr.Base.__eq__ = lambda a, b: clari.Create.eq(a, b)
clari.Expr.Base.__ne__ = lambda a, b: clari.Create.neq(a, b)

# Define new operators

# Comparisons
clari.Expr.Base.__le__ = lambda x, y: clari.Create.ule(x, y)
clari.Expr.Base.__lt__ = lambda x, y: clari.Create.ult(x, y)
clari.Expr.Base.__ge__ = lambda x, y: clari.Create.uge(x, y)
clari.Expr.Base.__gt__ = lambda x, y: clari.Create.ugt(x, y)
clari.Expr.FP.__le__ = lambda x, y: clari.Create.sle(x, y)
clari.Expr.FP.__lt__ = lambda x, y: clari.Create.slt(x, y)
clari.Expr.FP.__ge__ = lambda x, y: clari.Create.sge(x, y)
clari.Expr.FP.__gt__ = lambda x, y: clari.Create.sgt(x, y)

# Math

#

# Base: +, -, *, /
clari.Expr.Base.__pos__ = lambda x: x
clari.Expr.Base.__add__ = lambda *args: clari.Create.add(args)
clari.Expr.Base.__neg__ = lambda x: clari.Create.neg(x)
clari.Expr.Base.__sub__ = lambda x, y: clari.Create.sub(x, y)
clari.Expr.Base.__mul__ = lambda *args: clari.Create.mul(args)
# TODO: div

# Other: +, -, *, /
# TODO: these are not all __x__ methods?
# clari.Expr.FP.__add__ = lambda x,y: clari.Create.FP.add(x,y)
clari.Expr.String.__add__ = lambda x, y: clari.Create.concat(x, y)
# clari.Expr.FP.__sub__ = lambda x,y: clari.Create.FP.sub(x,y)
# clari.Expr.FP.__mul__ = lambda x,y: clari.Create.FP.mul(x,y) TODO: rounding mode
# clari.Expr.FP.__truediv__ = lambda x,y: clari.Create.FP.div(x,y) TODO: rounding mode
# TODO: sub = concat???

# TODO: div

clari.Expr.Base.__invert__ = lambda x: clari.Create.invert(x)


# Logical

# TODO: make segfault handler optional

# TODO: existing: format, new, reduce, reduce_ex, sizeof, str,

# TODO: __not__, is, is_not
# TODO: reverse operators?


if False:
    try:
        a = clari.Create.symbol_fp("f", 32)
        b = clari.Create.symbol_bv("b", 32)
        a + b
    except TypeError as e:
        print(e)
        print(type(e))
        import inspect

        print(inspect.getmro(type(e)))
        print(e.native_trace())
        print("Printed")
    finally:
        print("Fin")
        import IPython
        IPython.embed()
