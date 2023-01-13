import json

import pysmt
from pysmt.shortcuts import Symbol, get_env
from pysmt.smtlib.parser import SmtLibParser, PysmtSyntaxError


def make_pysmt_const_from_type(val, type):
    return getattr(pysmt.shortcuts, str(type))(val)


class SMTParser:
    def __init__(self, tokens):
        self.p = SmtLibParser()
        self.tokens = tokens

    def expect(self, *allowed):
        t = self.tokens.consume()
        if t not in allowed:
            raise PysmtSyntaxError(f"Invalid token, expected any of {allowed}, got '{t}'")
        return t

    def expect_assignment_tuple(self):
        self.expect("(")
        cmd = self.expect("define-fun")
        vname = self.p.parse_atom(self.tokens, cmd)
        self.expect("(")
        self.expect(")")
        t = self.p.parse_type(self.tokens, cmd)
        value = self.p.get_expression(self.tokens)
        self.expect(")")

        return Symbol(vname, t), getattr(pysmt.shortcuts, t.name)(value.constant_value())

    def consume_assignment_list(self):
        self.expect("(")
        self.expect("model")
        """Parses a list of expressions from the tokens"""

        assignments = []
        while True:
            next_token = self.tokens.consume()
            self.tokens.add_extra_token(next_token)  # push it back
            if next_token == ")":
                break

            assignments.append(self.expect_assignment_tuple())

        self.expect(")")

        return assignments
