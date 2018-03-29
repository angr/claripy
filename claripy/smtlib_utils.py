import json

import pysmt
from pysmt.shortcuts import Symbol
from pysmt.smtlib.parser import SmtLibParser, PysmtSyntaxError


class SMTParser(object):
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

        val = val_repr[1:-1] # strip quotes
        val = val.decode('string_escape') # decode escape sequences

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