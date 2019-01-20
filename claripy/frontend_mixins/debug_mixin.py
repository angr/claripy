call_depth = 0

def _log(s):
    print("|  " * call_depth + s)

def _debugged(f):
    def debugged(*args, **kwargs):
        global call_depth

        _log(f.__name__ + " " + str(args) + " " + str(kwargs))
        call_depth += 1
        try:
            r = f(*args, **kwargs)
        except Exception as e: #pylint:disable=broad-except
            r = "EXCEPTION: %s" % str(e)
            raise
        finally:
            call_depth -= 1
            if r is not None:
                _log(r"\... " + str(r))

        if hasattr(r, '__iter__') and hasattr(r, 'next'):
            return _debug_iterator(r)
        else:
            return r
    return debugged

def _debug_iterator(i):
    for v in i:
        _log("NEXT: " + str(v))
        yield v
    _log("FINISHED: " + str(i))

class DebugMixin:
    def __init__(self, *args, **kwargs):
        super(DebugMixin, self).__init__(*args, **kwargs)

    def __getattribute__(self, a):
        o = super(DebugMixin, self).__getattribute__(a)
        if a.startswith("__"):
            return o
        elif hasattr(o, '__call__'):
            return _debugged(o)
        elif hasattr(o, '__next__'):
            return _debug_iterator(o)
        else:
            return o

def debug_decorator(o):
    if isinstance(o, type):
        class Debugged(DebugMixin, o):
            pass
        Debugged.__name__ = "Debugged" + o.__name__
        return Debugged
    elif hasattr(o, '__call__'):
        return _debugged(o)
