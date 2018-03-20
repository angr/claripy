import json
import subprocess

from claripy import BackendError
from six.moves import cStringIO

import pysmt
from pysmt.smtlib.parser import SmtLibParser, SmtLib20Parser, Tokenizer, PysmtSyntaxError
from pysmt.shortcuts import Symbol, And, NotEquals

from .backend_smt import BackendSMT


class ParsedSMT(object):
    def __init__(self, tokens):
        self.p = SmtLibParser()
        self.tokens = tokens

    def expect(self, *allowed):
        t = self.tokens.consume()
        if t not in allowed:
            raise PysmtSyntaxError("Invalid token, expected any of {}, got '{}'".format(allowed, t))
        return t

    def expect_assignment_tuple(self):
        self.expect('(')
        self.expect('define-fun')
        vname = self.p.parse_atom(self.tokens, 'define-fun')
        self.expect('(')
        self.expect(')')
        t = self.p.parse_type(self.tokens, 'define-fun')
        val_repr = self.p.parse_atom(self.tokens, 'define-fun')
        self.expect(')')
        val = json.loads(val_repr).encode() # hacky, but works

        return Symbol(vname, t), getattr(pysmt.shortcuts, t.name)(val)

    def consume_assignment_list(self):
        self.expect('(')
        self.expect('model')
        """Parses a list of expressions from the tokens"""

        assignments = []
        while True:
            next_token = self.tokens.consume()
            self.tokens.add_extra_token(next_token)  # push it back
            if next_token == ')':
                break

            assignments.append(self.expect_assignment_tuple())

        self.expect(')')

        return assignments


class CVC4(object):
    def __init__(self):
        super(CVC4, self).__init__()
        self.p = subprocess.Popen(['cvc4', '--lang=smt', '-q', '--strings-exp'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def setup(self):
        self.writeline('(set-logic QF_SLIA)')
        self.writeline('(set-option :produce-models true)')

    def reset(self):
        self.write('(reset)\n')

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

    def writeline(self, l):
        return self.write(l + '\n')

    def read_sat(self):
        return self.readline().strip()

    def read_model(self):
        read_model = self.readuntil('\n)\n').strip()
        return read_model


class CVC4_Solver(CVC4):
    def __init__(self):
        super(CVC4_Solver, self).__init__()
        self.constraints = []

    def add_constraints(self, csts, track=False):
        self.constraints.extend(csts)


class BackendSMT_CVC4(BackendSMT):
    def __init__(self):
        super(BackendSMT_CVC4, self).__init__(solver_required=True)

    def solver(self, timeout=None): #pylint:disable=no-self-use,unused-argument
        """
        This function should return an instance of whatever object handles
        solving for this backend. For example, in Z3, this would be z3.Solver().
        """
        return CVC4_Solver()

    def _add(self, s, c, track=False):
        s.add_constraints(c, track=track)

    def _satisfiable(self, extra_constraints=(), solver=None, model_callback=None):
        smt_script = self._get_satisfiability_smt_script(tuple(extra_constraints) + tuple(solver.constraints))
        solver.reset()
        solver.write(smt_script)
        sat = solver.read_sat()
        return sat == 'sat'

    def _get_model(self, extra_constraints=(), solver=None):
        smt_script = self._get_full_model_smt_script(tuple(extra_constraints) + tuple(solver.constraints))
        solver.reset()
        solver.write(smt_script)
        sat = solver.read_sat()
        if sat == 'sat':
            model_string = solver.read_model()
            tokens = Tokenizer(cStringIO(model_string), interactive=True)
            ass_list = ParsedSMT(tokens).consume_assignment_list()
            return sat, {s.symbol_name(): val for s, val in ass_list}, ass_list
        else:
            error = solver.readline()

        return sat, error, None

    def _get_primitive_for_expr(self, model, e):
        if e.is_symbol():
            name = e.symbol_name()
            return model[name].constant_value()
        elif e.is_constant():
            return e.constant_value()
        else:
            raise BackendError("CVC4 backend currently only supports requests for symbols directly!")

    def _eval(self, expr, n, extra_constraints=(), solver=None, model_callback=None):
        e_c = list(extra_constraints)

        if expr.is_constant():
            return [expr.constant_value()]

        results = []
        while len(results) < n:
            sat, model, ass_list = self._get_model(extra_constraints=e_c, solver=solver)
            if sat != 'sat':
                break
            results.append(self._get_primitive_for_expr(model, expr))
            e_c.append(And(*[NotEquals(s, val) for s, val in ass_list]))

        return results

    def _batch_eval(self, exprs, n, extra_constraints=(), solver=None, model_callback=None):
        return [self._eval(e, n, extra_constraints=extra_constraints, solver=solver, model_callback=model_callback) for e in exprs]
