from .backend_smt import BackendSMT
import subprocess

def _expr_to_smtlib(e):
    if e.is_symbol():
        return "(declare-const %s %s)" % (e.symbol_name(), e.symbol_type())
    else:
        return "(assert %s)" % e.to_smtlib()

def _exprs_to_smtlib(*exprs):
    return '\n'.join(_expr_to_smtlib(e) for e in exprs) + '\n'

class CVC4(object):
    def __init__(self):
        super(CVC4, self).__init__()
        self.p = subprocess.Popen(['cvc4', '--lang=smt', '-q'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def _readuntil(self, s):
        buf = ''
        while s not in buf:
            buf += self.p.stdout.read(1)
        return buf

    def _readline(self):
        return self._readuntil('\n')

    def write(self, smt):
        self.p.stdin.write(smt)
        self.p.stdin.flush()

    def reset(self):
        self.write('(reset)\n')

    def read_sat(self):
        return self._readline().strip()

    def read_model(self):
        return self._readuntil('\n)\n').strip()

class BackendSMT_CVC4(BackendSMT):
    def __init__(self):
        super(BackendSMT_CVC4, self).__init__()
        self.cvc4 = CVC4()

    def _smtlib_exprs(self, extra_constraints=()):
        all_exprs = tuple(self._assertions_stack) + tuple(extra_constraints)
        return _exprs_to_smtlib(*all_exprs)

    def _get_satisfiability_smt_script(self, extra_constraints=()):
        '''
        Returns a SMT script that declare all the symbols and constraint and checks
        their satisfiability (check-sat)
        '''
        smt_script = '(set-logic ALL)\n'
        smt_script += self._smtlib_exprs(extra_constraints)
        smt_script += '(check-sat)\n'
        return smt_script

    def _get_full_model_smt_script(self, extra_constraints=()):
        '''
        Returns a SMT script that declare all the symbols and constraint and checks
        their satisfiability (check-sat)
        '''
        smt_script = '(set-logic ALL)\n'
        smt_script += '(set-option :produce-models true)\n'
        smt_script += self._smtlib_exprs(extra_constraints)
        smt_script += '(check-sat)\n'
        smt_script += '(get-model)\n'
        return smt_script

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
        sat = self.cvc4.read_sat() == 'sat'
        model = self.cvc4.read_model()
        return sat, model
