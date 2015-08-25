import copy
import collections
import weakref

import threading

class Result(object):
    def __init__(self, satness, model=None, approximation=False, backend_model=None):
        self.sat = satness
        self.model = model if model is not None else { }
        self._tls = threading.local()
        self._tls.backend_model = backend_model
        self.approximation = approximation
        self.eval_cache = { }
        self.min_cache = { }
        self.max_cache = { }
        self.resolve_cache = collections.defaultdict(weakref.WeakKeyDictionary)

    @property
    def backend_model(self):
        try:
            return self._tls.backend_model
        except AttributeError:
            return None

    def branch(self):
        r = Result(self.sat, copy.copy(self.model), backend_model=self._tls.backend_model)
        r.eval_cache = dict(self.eval_cache)
        r.min_cache = dict(self.min_cache)
        r.max_cache = dict(self.max_cache)
        return r

    def __getstate__(self):
        return ( self.sat, self.model, self.eval_cache, self.min_cache, self.max_cache )

    def __setstate__(self, state):
        ( self.sat, self.model, self.eval_cache, self.min_cache, self.max_cache ) = state
        self.resolve_cache = collections.defaultdict(weakref.WeakKeyDictionary)
        self._tls = threading.local()
        self._tls.backend_model = None

    def downsize(self):
        self._tls.backend_model = None

def UnsatResult(**kwargs):
    return Result(False, **kwargs)

def SatResult(**kwargs):
    return Result(True, **kwargs)
