from enum import Enum
import clari
import logging
import functools

logging.basicConfig(
    level=logging.DEBUG, # TODO: use angr logging system
    format='%(levelname)-7s | %(asctime)-23s | %(name)-8s | %(message)s'
)

### Exceptions grab extra info

clari.Util.Err.Claricpp.toggle_backtrace(True) # TODO: remove me when not debugging
def _cls_init(self, *args, **kwargs):
    def native_trace(args):
        if not hasattr(self, '_native_trace'):
            lazy = args[0]
            if lazy is None:
                self._native_trace = ""
            else:
                try:
                    self._native_trace = lazy.str() # Evaluate and cache the result
                except Exception as e:
                    logging.error("Failed to extract native backtrace because: " + str(e))
                    self._native_trace = ""
            del args[0] # Free the lazy object since we cached the evaluation
        return self._native_trace
    lazy = clari.Util.Err.Claricpp.lazy_backtrace() # should never throw
    # Set the native_trace function and call the old init
    self.native_trace = functools.partial(native_trace, [lazy])
    super(clari.py_err._internal.Base, self).__init__(*args, **kwargs)
clari.py_err._internal.Base.__init__ = _cls_init
del _cls_init # No need to keep this name around

### Init clari

# Set claricpp log level to debug
# Note: the python log level still defines which messages are printed
# This simply defines if claricpp even bothers to send a message to python
clari.API.set_log_propagation_level(logging.DEBUG)
clari.API.install_logger(lambda a,b,c: logging.getLogger(a).log(b,c))

### Operators ###

# Fixes
# TODO: make this work for instance variabels clari.Expr.Base.args = clari.Expr.Base.python_children

# Define repr
# TODO: clari.Annotation.Base.__repr__ = clari.Annotation.Base.repr
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
clari.Expr.Base.__eq__ = lambda a,b: clari.Create.eq(a,b)
clari.Expr.Base.__ne__ = lambda a,b: clari.Create.neq(a,b)

# Define new operators

# Comparisons
clari.Expr.Base.__le__ = lambda x,y: clari.Create.ule(x,y)
clari.Expr.Base.__lt__ = lambda x,y: clari.Create.ult(x,y)
clari.Expr.Base.__ge__ = lambda x,y: clari.Create.uge(x,y)
clari.Expr.Base.__gt__ = lambda x,y: clari.Create.ugt(x,y)
clari.Expr.FP.__le__ = lambda x,y: clari.Create.sle(x,y)
clari.Expr.FP.__lt__ = lambda x,y: clari.Create.slt(x,y)
clari.Expr.FP.__ge__ = lambda x,y: clari.Create.sge(x,y)
clari.Expr.FP.__gt__ = lambda x,y: clari.Create.sgt(x,y)

# Math

#

# Base: +, -, *, /
clari.Expr.Base.__pos__ = lambda x: x
clari.Expr.Base.__add__ = lambda *args: clari.Create.add(args)
clari.Expr.Base.__neg__ = lambda x: clari.Create.neg(x)
clari.Expr.Base.__sub__ = lambda x,y: clari.Create.sub(x,y)
clari.Expr.Base.__mul__ = lambda *args: clari.Create.mul(args)
# TODO: div

# Other: +, -, *, /
# TODO: these are not all __x__ methods?
# clari.Expr.FP.__add__ = lambda x,y: clari.Create.FP.add(x,y)
clari.Expr.String.__add__ = lambda x,y: clari.Create.concat(x,y)
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