import weakref
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


# TODO: remove clari.Create.foo from callbacks (dict lookups are costly)

##################################################
###         Link Claricpp and Claripy          ###
##################################################


### Logging


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
clari.API.add_source_root(os.path.join(os.path.dirname(clari.__file__))) # TODO: make this better
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


### Defaults


clari.Mode.FP.Rounding.default = lambda: clari.Mode.FP.Rounding.NearestTiesEven


##################################################
###                 Operators                  ###
##################################################
# TODO: reverse operators __radd__ etc


### Fixes

# Equality (bindings default to pointer equality)
clari.Expr.Base.__eq__ = lambda a, b: clari.Create.eq(a, b)
clari.Expr.Base.__ne__ = lambda a, b: clari.Create.neq(a, b)

# Hashing
clari.Annotation.Base.__hash__ = lambda x: x.hash
clari.Annotation.Vec.__hash__ = lambda x: x.hash
clari.Expr.Base.__hash__ = lambda x: x.hash
clari.Op.Base.__hash__ = lambda x: x.hash

# repr (ignore pybind11 defaults)
clari.Annotation.Base.__repr__ = clari.Annotation.Base.repr
clari.Annotation.Vec.__repr__ = clari.Annotation.Vec.repr
clari.Expr.Base.__repr__ = clari.Expr.Base.repr
clari.Op.Base.__repr__ = clari.Op.Base.repr

### Base

# TODO: ask fish __sizeof__ base.py # z3 backend uses getsizeof
# TODO: ask fish __reduce__ base.py
clari.Expr.Base.__pos__ = lambda x: x # TODO: ask fish

### Bits

clari.Expr.Bits.__len__ = lambda x: x.bit_length

### Bool

clari.Expr.Bool.__invert__ = lambda x: clari.Create.invert(x)
clari.Expr.Bool.__not__ = lambda x: clari.Create.invert(x) # TODO: ask fish
clari.Expr.Bool.__and__ = lambda x: clari.Create.and_(x)
clari.Expr.Bool.__xor__ = lambda x: clari.Create.xor_(x) # TODO: ask fish
clari.Expr.Bool.__or__ = lambda x: clari.Create.or_(x)

### BV

# Comparisons
clari.Expr.BV.__le__ = lambda x, y: clari.Create.ule(x, y)
clari.Expr.BV.__lt__ = lambda x, y: clari.Create.ult(x, y)
clari.Expr.BV.__ge__ = lambda x, y: clari.Create.uge(x, y)
clari.Expr.BV.__gt__ = lambda x, y: clari.Create.ugt(x, y)

# Logical
clari.Expr.BV.__invert__ = lambda x: clari.Create.invert(x)
clari.Expr.BV.__and__ = lambda x: clari.Create.and_(x)
clari.Expr.BV.__xor__ = lambda x: clari.Create.xor_(x)
clari.Expr.BV.__or__ = lambda x: clari.Create.or_(x)

# +, -, *, /
clari.Expr.BV.__neg__ = lambda x: clari.Create.neg(x)
clari.Expr.BV.__add__ = lambda *args: clari.Create.add(args)
clari.Expr.BV.__mul__ = lambda *args: clari.Create.mul(args)
clari.Expr.BV.__sub__ = lambda x, y: clari.Create.sub(x, y)
clari.Expr.BV.__floordiv__ = lambda x, y: clari.Create.div(x, y)
clari.Expr.BV.__truediv__ = clari.Expr.BV.__floordiv__ # TODO: get this removed (should be legacy)

# Other
clari.Expr.BV.__abs__ = lambda x: clari.Create.abs(x)
clari.Expr.BV.__pow__ = lambda a, b: clari.Create.pow(a, b)
clari.Expr.BV.__mod__ = lambda a, b: clari.Create.mod(a, b)
clari.Expr.BV.__lshift__ = lambda a, b: clari.Create.shift_l(a, b)
clari.Expr.BV.__rshift__ = lambda a, b: clari.Create.shift_arithmetic_right(a, b)

### FP

# Comparisons
clari.Expr.FP.__le__ = lambda x, y: clari.Create.sle(x, y)
clari.Expr.FP.__lt__ = lambda x, y: clari.Create.slt(x, y)
clari.Expr.FP.__ge__ = lambda x, y: clari.Create.sge(x, y)
clari.Expr.FP.__gt__ = lambda x, y: clari.Create.sgt(x, y)

# +, -, *, /
rm = clari.Mode.FP.Rounding.default
clari.Expr.FP.__neg__ = lambda x: clari.Create.neg(x)
clari.Expr.FP.__add__ = lambda x, y: clari.Create.FP.add(x, y, rm)
clari.Expr.FP.__sub__ = lambda x, y: clari.Create.FP.sub(x, y, rm)
clari.Expr.FP.__mul__ = lambda x, y: clari.Create.FP.mul(x, y, rm)
clari.Expr.FP.__truediv__ = lambda x, y: clari.Create.FP.div(x, y, rm)
del rm

# Other
clari.Expr.FP.__abs__ = lambda x: clari.Create.abs(x)

### String

clari.Expr.String.__add__ = lambda x, y: clari.Create.concat(x, y)

### Useful functions



### Legacy support


# Claricpp objects are generally readonly
# This is a internal mapping from weak references to cached args
clari.Expr.Base._args_dict = weakref.WeakKeyDictionary()

# Define .args for claricpp objects
def _args(self):
    if self not in self._args_dict:
        lst = self.op.python_children()
        print(type(self.op))
        if self.op.is_leaf:
            lst.append(len(self))
        self._args_dict[self] = tuple(lst)
    return self._args_dict[self]
clari.Expr.Base.args = property(_args)
del _args



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
