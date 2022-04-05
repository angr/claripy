from enum import Enum
import clari
import logging

logging.basicConfig(
    level=logging.DEBUG, # TODO: use angr logging system
    format='%(levelname)-7s | %(asctime)-23s | %(name)-8s | %(message)s'
)

### Exceptions grab extra info

clari.Util.Err.Claricpp.toggle_backtrace(True) # TODO: remove me when not debugging
def _cls_init(self, *args, **kwargs):
    tr = clari.Util.Err.Claricpp.backtrace()
    self.native_trace = tr if len(tr) > 0 else "Native tracing is disabled"
    super(clari.py_err._internal.Base, self).__init__(*args, **kwargs)
clari.py_err._internal.Base.__init__ = _cls_init
del _cls_init # No need to keep this name around

### Init clari

# Set claricpp log level to debug
# Note: the python log level still defines which messages are printed
# This simply defines if claricpp even bothers to send a message to python
clari.API.set_log_propagation_level(logging.DEBUG)
clari.API.install_logger(lambda a,b,c: logging.getLogger(a).log(b,c))

### Fix / define operators

# Passthrough
clari.Expr.Base.__hash__ = lambda x: x.hash
clari.Expr.Base.__repr__ = clari.Expr.Base.repr

# Equality
clari.Expr.Base.__eq__ = lambda a,b: clari.Create.eq(a,b)
clari.Expr.Base.__ne__ = lambda a,b: clari.Create.neq(a,b)

# Comparisons
clari.Expr.Base.__le__ = lambda x,y: clari.Create.ule(x,y)
clari.Expr.Base.__lt__ = lambda x,y: clari.Create.ult(x,y)
clari.Expr.Base.__ge__ = lambda x,y: clari.Create.uge(x,y)
clari.Expr.Base.__gt__ = lambda x,y: clari.Create.ugt(x,y)
clari.Expr.FP.__le__ = lambda x,y: clari.Create.sle(x,y)
clari.Expr.FP.__lt__ = lambda x,y: clari.Create.slt(x,y)
clari.Expr.FP.__ge__ = lambda x,y: clari.Create.sge(x,y)
clari.Expr.FP.__gt__ = lambda x,y: clari.Create.sgt(x,y)

# TODO: define new ops! +, -, etc

# TODO: exception init
a = clari.Create.literal(5)
b = clari.Create.literal(5.0)
print("Doing cmp")
print(repr(a.op))
print(repr(a < a))
print(repr(b < b))

print("\n\n")
try:
    clari.Create.sge(a,b)
except Exception as e:
    ts = '  '
    print("\nCaught exception:\n" + ts + "msg: " + str(e))
    print(ts + "type: " + str(type(e)))
    import inspect
    mro = [ str(i).split("'")[1] for i in inspect.getmro(type(e)) ]
    print(ts + "mro:\n" + ts*2 + ('\n'+ts*2).join(mro))
    print('\n' + ts + "e.native_trace:\n\n" + e.native_trace)
    ln = '\n' + '*' * 70
    print(ln + '\n*' + 'End of exception info'.center(68, ' ') + '*' + ln + '\n')

    import IPython
    IPython.embed()


# Logical


# TODO: existing: format, new, reduce, reduce_ex, sizeof, str,

# TODO: __not__, is, is_not
# TODO: reverse operators?
