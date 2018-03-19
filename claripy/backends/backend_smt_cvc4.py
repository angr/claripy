from .backend_smt import BackendSMT
import subprocess
from pysmt.smtlib.parser import SmtLibParser
from six.moves import cStringIO



class CVC4(object):
    def __init__(self):
        super(CVC4, self).__init__()
        self.p = subprocess.Popen(['cvc4', '--lang=smt', '-q'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def read(self, n):
        return self.p.stdout.read(n)

    def readuntil(self, s):
        buf = ''
        while s not in buf:
            buf += self.p.stdout.read(1)
        return buf

    def readline(self):
        return self.readuntil('\n')

    def write(self, smt):
        self.p.stdin.write(smt)
        self.p.stdin.flush()

    def reset(self):
        self.write('(reset)\n')

    def read_sat(self):
        return self.readline().strip()

    def read_model(self):
        read_model = self.readuntil('\n)\n').strip()
        return read_model


class BackendSMT_CVC4(BackendSMT):
    def __init__(self):
        super(BackendSMT_CVC4, self).__init__()
        self.cvc4 = CVC4()
        self.smtlib_parser = SmtLibParser()

    def _satisfiable(self, extra_constraints=(), solver=None, model_callback=None):
        smt_script = self._get_satisfiability_smt_script(extra_constraints)
        self.cvc4.reset()
        self.cvc4.write(smt_script)
        sat = self.cvc4.read_sat()
        return sat == 'sat'

    def _get_model(self, extra_constraints=()):
        smt_script = self._get_full_model_smt_script(extra_constraints)
        self.cvc4.reset()
        self.cvc4.write(smt_script)
        sat = self.cvc4.read_sat()
        if sat == 'sat':
            model_string = self.cvc4.read_model()
            ass_list = self.smtlib_parser.get_assignment_list(cStringIO(model_string))
            return sat, ass_list
        else:
            error = self.cvc4.readline()

        return sat, error
