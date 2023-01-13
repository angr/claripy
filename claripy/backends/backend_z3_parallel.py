import os
import pickle
import threading

num_children = 0

import logging

l = logging.getLogger("claripy.backends.backend_z3_parallel")

from .backend_z3 import BackendZ3


class BackendZ3Parallel(BackendZ3):
    def __init__(self):
        BackendZ3.__init__(self)
        self._child = False
        self._lock = threading.RLock()
        self._cache_objects = False

    def _background(self, f_name, *args, **kwargs):
        global num_children

        f = getattr(BackendZ3, f_name)
        if self._child:
            return f(self, *args, **kwargs)

        p_r, p_w = os.pipe()
        p = os.fork()

        if p == 0:
            self._child = True
            self._lock = threading.RLock()
            try:
                r = f(self, *args, **kwargs)
            except UnsatError as e:
                r = e

            # print("WRITING (%d)" % os.getpid())
            pickled = pickle.dumps(r, -1)
            written = 0
            while written < len(pickled):
                written += os.write(p_w, pickled[written:])
            os.close(p_w)
            os.close(p_r)
            # print("WROTE (%d)" % os.getpid())

            os.kill(os.getpid(), 9)
            # os.abort()
            # sys.exit(1)
        else:
            os.close(p_w)

            num_children += 1
            l.debug("in _background with function %s and child %d (among %d)", f, p, num_children)

            # print("READING (from %d)" % p)
            try:
                strs = [os.read(p_r, 1024 * 1024)]
                while strs[-1] != "":
                    strs.append(os.read(p_r, 1024 * 1024))
            except EOFError:
                raise ClaripyError("read error while receiving data from child")
            os.close(p_r)
            # print("READ (from %d)" % p)

            # thread.start_new_thread(os.wait, ())
            r = pickle.loads("".join(strs))

            os.waitpid(p, 0)
            num_children -= 1
            l.debug("... child %d is done. %d left", p, num_children)

            if isinstance(r, Exception):
                raise r
            else:
                return r

    def _synchronize(self, f, *args, **kwargs):
        if self._child:
            return getattr(BackendZ3, f)(self, *args, **kwargs)

        self._lock.acquire()
        # while not self._lock.acquire(blocking=False): print("ACQUIRING...",__import__('time').sleep(1))
        try:
            return getattr(BackendZ3, f)(self, *args, **kwargs)
        finally:
            self._lock.release()

    @staticmethod
    def _translate(*args):
        for a in args:
            if hasattr(a, "translate"):
                a.translate()

    # backgrounded
    def _results(self, *args, **kwargs):
        return self._background("_results", *args, **kwargs)

    def _eval(self, *args, **kwargs):
        return self._background("_eval", *args, **kwargs)

    def _batch_eval(self, *args, **kwargs):
        return self._background("_batch_eval", *args, **kwargs)

    def _min(self, *args, **kwargs):
        return self._background("_min", *args, **kwargs)

    def _max(self, *args, **kwargs):
        return self._background("_max", *args, **kwargs)

    def _convert(self, *args, **kwargs):
        return self._synchronize("_convert", *args, **kwargs)

    def abstract(self, *args, **kwargs):
        return self._synchronize("abstract", *args, **kwargs)

    def solver(self, *args, **kwargs):
        return self._synchronize("solver", *args, **kwargs)

    def _add(self, *args, **kwargs):
        return self._synchronize("_add", *args, **kwargs)

    def _check(self, *args, **kwargs):
        return self._synchronize("_check", *args, **kwargs)

    def _simplify(self, *args, **kwargs):
        return self._synchronize("_simplify", *args, **kwargs)

    def call(self, *args, **kwargs):
        return self._synchronize("call", *args, **kwargs)

    def resolve(self, *args, **kwargs):
        return self._synchronize("resolve", *args, **kwargs)

    def simplify(self, *args, **kwargs):
        return self._synchronize("simplify", *args, **kwargs)


from ..errors import ClaripyError, UnsatError
