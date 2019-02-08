class EvalStringsToASTsMixin(object):
    def eval_to_ast(self, e, n, extra_constraints=(), exact=None):
        if type(e) is String:
            return [StringV(v, ) for v in self.eval(e, n, extra_constraints=extra_constraints, exact=exact) ]

        return super(EvalStringsToASTsMixin, self).eval_to_ast(e, n, extra_constraints=extra_constraints, exact=None)

from .. import String, StringV
