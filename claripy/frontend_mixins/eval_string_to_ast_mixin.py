from __future__ import annotations

from claripy import String, StringV


class EvalStringsToASTsMixin:
    def eval_to_ast(self, e, n, extra_constraints=(), exact=None):
        if type(e) is String:
            return [
                StringV(
                    v,
                )
                for v in self.eval(e, n, extra_constraints=extra_constraints, exact=exact)
            ]

        return super().eval_to_ast(e, n, extra_constraints=extra_constraints, exact=None)
