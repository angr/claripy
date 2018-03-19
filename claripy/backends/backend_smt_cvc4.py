import json
import subprocess

from six.moves import cStringIO

import pysmt
from pysmt.smtlib.parser import SmtLibParser, SmtLib20Parser, Tokenizer, PysmtSyntaxError
from pysmt.shortcuts import Symbol

from .backend_smt import BackendSMT

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
        val = json.loads(val_repr) # hacky, but works

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


class BackendSMT_CVC4(BackendSMT):
    def __init__(self):
        super(BackendSMT_CVC4, self).__init__(solver_required=True)

    def solver(self, timeout=None): #pylint:disable=no-self-use,unused-argument
        """
        This function should return an instance of whatever object handles
        solving for this backend. For example, in Z3, this would be z3.Solver().
        """
        return CVC4()

    def _satisfiable(self, extra_constraints=(), solver=None, model_callback=None):
        smt_script = self._get_satisfiability_smt_script(extra_constraints)
        solver.reset()
        solver.write(smt_script)
        sat = solver.read_sat()
        return sat == 'sat'

    def _get_model(self, extra_constraints=(), solver=None):
        smt_script = self._get_full_model_smt_script(extra_constraints)
        solver.reset()
        solver.write(smt_script)
        sat = solver.read_sat()
        if sat == 'sat':
            model_string = solver.read_model()
            tokens = Tokenizer(cStringIO(model_string), interactive=True)
            ass_list = ParsedSMT(tokens).consume_assignment_list()
            return sat, ass_list
        else:
            error = solver.readline()

        return sat, error


'''
# from http://probablyprogramming.com/2009/11/23/a-simple-lisp-parser-in-python

from string import whitespace

atom_end = set('()"\'') | set(whitespace)

def parse(sexp):
    stack, i, length = [[]], 0, len(sexp)
    while i < length:
        c = sexp[i]

        print c, stack
        reading = type(stack[-1])
        if reading == list:
            if   c == '(': stack.append([])
            elif c == ')':
                stack[-2].append(stack.pop())
                if stack[-1][0] == ('quote',): stack[-2].append(stack.pop())
            elif c == '"': stack.append('')
            elif c == "'": stack.append([('quote',)])
            elif c in whitespace: pass
            else: stack.append((c,))
        elif reading == str:
            if   c == '"':
                stack[-2].append(stack.pop())
                if stack[-1][0] == ('quote',): stack[-2].append(stack.pop())
            elif c == '\\':
                i += 1
                stack[-1] += sexp[i]
            else: stack[-1] += c
        elif reading == tuple:
            if c in atom_end:
                atom = stack.pop()
                if atom[0][0].isdigit(): stack[-1].append(eval(atom[0]))
                else: stack[-1].append(atom)
                if stack[-1][0] == ('quote',): stack[-2].append(stack.pop())
                continue
            else: stack[-1] = ((stack[-1][0] + c),)
        i += 1
    return stack.pop()
'''
