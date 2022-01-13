__all__ = [ 'ffi', 'to_utf8', 'claricpp', 'ClaricppException' ]

import os
import sys
import functools
import logging

sys.path.append(os.environ['CLARICPP_FFI_LIB_DIR']) # TODO
from claricpp_ffi import ffi, lib as raw_lib
sys.path.pop()

# TODO: slots!

# Init
logging.basicConfig(level=logging.DEBUG, format='%(levelname)-7s | %(asctime)-23s | %(name)-8s | %(message)s')


# Helpers
def to_utf8(cdata) -> str:
    '''
    Convert a char * to a str
    '''
    if cdata != ffi.NULL:
        return ffi.string(cdata).decode('utf-8') # TODO: this is slow
    return ''

# Callbacks
@ffi.def_extern()
def claripy_log(id_, lvl, msg):
    '''
    Claricpp's log callback
    '''
    logging.getLogger(name=to_utf8(id_)).log(level=lvl, msg=to_utf8(msg))
@ffi.def_extern()
def claripy_level(id_):
    '''
    Claricpp's 'get log level' callback
    '''
    return logging.getLogger(name=to_utf8(id_)).getEffectiveLevel()

# Exceptions
class ClaricppException(Exception):
    '''
    The exception type claricpp throws for an internal error
    '''
    def __init__(self, exc):
        self.type = exc.type
        self.msg: str = to_utf8(exc.msg)
        self.trace: str = to_utf8(exc.trace)
        super().__init__(repr(self))
    def __repr__(self):
        return 'Type: ' + str(self.type) + '\nMsg: ' + self.msg + '\nTrace: ' + self.trace + '\n\nEND OF EXCEPTION'

# Claricpp helpers
def wrap(func):
    '''
    Wrap a raw_lib function call with exception handling
    '''
    @functools.wraps(func)
    def internal(*args, **kwargs):
        res = func(*args, **kwargs)
        if bool(raw_lib.claricpp_has_exception()):
            # TODO: function which determines if this should be a python exception or a claricpp one
            raise ClaricppException(raw_lib.claricpp_get_exception()) # from somewhere???
        return res
    return internal

# Wrap raw_lib to handle exceptions
class Claricpp:
    '''
    Wraps raw_lib with exception handling code
    '''
    def __getattribute__(self, attr):
        '''
        When a function is requested, return the wrapped version
        We make exceptions for the exception handling functions to prevent infinite loops
        '''
        got = getattr(raw_lib, attr)
        exempt = ['claricpp_get_exception', 'claricpp_has_exception']
        if hasattr(got, '__call__') and attr not in exempt:
            return wrap(got)
        return got

# Claricpp
claricpp = Claricpp()

# Configure Claricpp for use with python
# TODO: only run on first import
claricpp.claricpp_init_for_python_usage(raw_lib.claripy_log, raw_lib.claripy_level)
