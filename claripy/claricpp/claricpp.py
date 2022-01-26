__all__ = ["ffi", "to_utf8", "claricpp", "ClaricppException"]

import sys
import functools
import logging
from .claricpp_ffi import ffi, lib as raw_lib

# TODO: slots!

# Init
logging.basicConfig(
    level=logging.DEBUG,
    format="%(levelname)-7s | %(asctime)-23s | %(name)-8s | %(message)s",
)


# Helpers
def to_utf8(cdata) -> str:
    """
    Convert a char * to a str
    """
    if cdata != ffi.NULL:
        return ffi.string(cdata).decode("utf-8")  # TODO: this is slow
    return ""


# Callbacks
@ffi.def_extern()
def claripy_log(id_, lvl, msg):
    """
    Claricpp's log callback
    """
    logging.getLogger(name=to_utf8(id_)).log(level=lvl, msg=to_utf8(msg))


@ffi.def_extern()
def claripy_level(id_):
    """
    Claricpp's 'get log level' callback
    """
    return logging.getLogger(name=to_utf8(id_)).getEffectiveLevel()


@ffi.def_extern()
def claripy_simplify(expr):
    """
    Claricpp's python shell out to simplify
    """
    logging.debug("Python simplifier callback invoked")
    return expr


######################################################################
#                         Library Exceptions                         #
######################################################################

# Exceptions @todo: Update python traceback with C++ trace info
class ClaricppException(Exception):
    """
    The exception type claricpp throws for an internal error
    """

    def __init__(self, exc):
        self.type = exc.type
        self.msg: str = to_utf8(exc.msg)
        self.trace: str = to_utf8(exc.trace)
        super().__init__(repr(self))

    def msg_trace(self):
        return (
            "Type: " + str(self.type) + "\nMsg: " + self.msg + "\nTrace: " + self.trace
        )

    def __repr__(self):
        return "Type: " + str(self.type) + "\n" + msg_trace() + "\n\nEND OF TRACE"


# 'Crash now' exception handlers


def alloc_fail(_):
    logging.critical(
        "Memory allocation failure within claricpp; memory may be corrupted"
    )
    raise OSError("Cannot allocate memory")


def fail_critical(ex):
    logging.critical("Critical claricpp error detected. Please report this.")
    logging.critical("Given error: " + ex)
    logging.critical("Terminating program")
    raise SystemExit(1)


# Fallbacks (report these)


def unknown_exception(ex):
    logging.critical(
        "Unknown exception type raised; claricpp does not recognize the error. Please report this."
    )
    raise ex


def std_exception(ex):
    logging.critical("Uncaught std::exception in claricpp. Please report this.")
    raise ex


def unexpected_exception(ex):
    logging.critical("Intnernal claricpp error. Please report this.")
    raise ex


def unknown_py_exception(ex):
    logging.critical("Unknown python exception raised in claricpp. Please report this.")
    raise Exception("Given Error: " + repr(ex))


def unknown_claripy(ex):
    logging.critical(
        "Unknown claripy exception raised in claricpp. Please report this."
    )
    raise Exception("Given Error: " + repr(ex))  # @todo: claripy exception


# Direct mappings
def _map_ex_to_func(typ):
    def f(ex):
        raise typ(ex.msg_trace())

    return f


# Maps exception types to corresponding functions
exception_map = {
    # Crash now
    raw_lib.ClaricppExceptionEnumFailAlloc: alloc_fail,
    raw_lib.ClaricppExceptionEnumFailCritical: fail_critical,
    # Fallbacks (report these)
    raw_lib.ClaricppExceptionEnumUnknown: unknown_exception,
    raw_lib.ClaricppExceptionEnumStd: std_exception,
    raw_lib.ClaricppExceptionEnumUnexpected: unexpected_exception,
    raw_lib.ClaricppExceptionEnumPython: unknown_py_exception,
    raw_lib.ClaricppExceptionEnumClaripy: unknown_claripy,
    # Direct mappings
    raw_lib.ClaricppExceptionRuntimeError: _map_ex_to_func(RuntimeError)
    # claricpp.ClaricppExceptionEnumExprType          : @todo
    # claricpp.ClaricppExceptionEnumExprUsage         : @todo
    # claricpp.ClaricppExceptionEnumExprValue         : @todo
    # claricpp.ClaricppExceptionEnumExprSize          : @todo
    # claricpp.ClaricppExceptionEnumExprOperation     : @todo
    # claricpp.ClaricppExceptionEnumBackendAbstraction: @todo
    # claricpp.ClaricppExceptionEnumBackendUnsupported: @todo
}


######################################################################
#                            Library Wrap                            #
######################################################################


# Claricpp helpers
def wrap(func):
    """
    Wrap a raw_lib function call with exception handling
    """

    @functools.wraps(func)
    def internal(*args, **kwargs):
        res = func(*args, **kwargs)
        if bool(raw_lib.claricpp_has_exception()):
            ex = ClaricppException(raw_lib.claricpp_get_exception())
            exception_map[ex.type](ex)
        return res

    return internal


# Wrap raw_lib to handle exceptions
class Claricpp:
    """
    Wraps raw_lib with exception handling code
    """

    def __getattribute__(self, attr):
        """
        When a function is requested, return the wrapped version
        We make exceptions for the exception handling functions to prevent infinite loops
        """
        got = getattr(raw_lib, attr)
        exempt = ["claricpp_get_exception", "claricpp_has_exception"]
        if hasattr(got, "__call__") and attr not in exempt:
            return wrap(got)
        return got


######################################################################
#                            Library Init                            #
######################################################################


# Claricpp
claricpp = Claricpp()

# Configure Claricpp for use with python
# TODO: only run on first import
claricpp.claricpp_init_for_python_usage(
    raw_lib.claripy_log, raw_lib.claripy_level, raw_lib.claripy_simplify
)
