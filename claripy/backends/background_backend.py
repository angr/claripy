import os
import pickle

from .solver_backend import SolverBackend

class BackgroundBackend(SolverBackend):
	def __init__(self, backend):
		SolverBackend.__init__(self, backend._claripy)
		self._backend = backend

	def _background(self, f, *args, **kwargs):
		f = getattr(self._backend, f)
		p_r, p_w = os.pipe()
		p = os.fork()
		if p == 0:
			try:
				r = f(*args, **kwargs)
			except UnsatError as e:
				r = e

			#print "WRITING (%d)" % os.getpid()
			pickled = pickle.dumps(r)
			written = 0
			while written < len(pickled):
				written += os.write(p_w, pickled[written:])
			os.close(p_w)
			os.close(p_r)
			#print "WROTE (%d)" % os.getpid()
			os.kill(os.getpid(), 9)
			#os.abort()
			#sys.exit(1)
		else:
			os.close(p_w)
			#print "READING (from %d)" % p
			try:
				strs = [ os.read(p_r, 1024*1024) ]
				while strs[-1] != "": strs.append(os.read(p_r, 1024*1024))
			except EOFError:
				raise Exception("WTF")
			os.close(p_r)
			#print "READ (from %d)" % p

			#thread.start_new_thread(os.wait, ())
			r = pickle.loads("".join(strs))
			if isinstance(r, Exception): raise r
			else: return r

from ..result import UnsatError
