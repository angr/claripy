call_depth = 0

def _debugged(f):
    def debugged(*args, **kwargs):
        global call_depth

        print "|  " * call_depth + f.__name__ + " " + str(args) + " " + str(kwargs)
        call_depth += 1
        try:
            r = f(*args, **kwargs)
        except Exception as e: #pylint:disable=broad-except
            r = "EXCEPTION: %s" % str(e)
            raise
        finally:
            call_depth -= 1
            if r is not None:
                print "|  " * call_depth + r"\... " + str(r)
        return r
    return debugged

class DebugMixin(object):
    def __init__(self, *args, **kwargs):
        super(DebugMixin, self).__init__(*args, **kwargs)

    def __getattribute__(self, a):
        o = super(DebugMixin, self).__getattribute__(a)
        if a.startswith("__") or not hasattr(o, '__call__'):
            return o
        else:
            return _debugged(o)

def debug_decorator(o):
    if isinstance(o, type):
        class Debugged(DebugMixin, o):
            pass
        Debugged.__name__ = "Debugged" + o.__name__
        return Debugged
    elif hasattr(o, '__call__'):
        return _debugged(o)
