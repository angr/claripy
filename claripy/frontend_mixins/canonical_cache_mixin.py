from ..solver_cache import global_solution_cache
from ..ast.structure import ASTStructure, get_structure_form
from ..ast.base import Base
from .. import And
import logging

l = logging.getLogger("claripy.frontend_mixins.canonical_cache_mixin")

def replace_unsats(constraints):
    return [constraint.swap_structure(
              get_structure_form(constraint).canonically_replace(global_solution_cache.unsats, is_hashmap=True)
            )
            for constraint in constraints if isinstance(constraint, ASTStructure)
                                          or isinstance(constraint, Base)]

class CanonicalCacheMixin(object):
    def __init__(self, *args, **kwargs):
        super(CanonicalCacheMixin, self).__init__(*args, **kwargs)

    def simplify(self):
        new = super(CanonicalCacheMixin, self).simplify()
        replaced = replace_unsats(new)
        return replaced

    def add(self, constraints, **kwargs):
        replaced = replace_unsats(constraints)
        return super(CanonicalCacheMixin, self).add(replaced, **kwargs)

    def satisfiable(self, extra_constraints=(), **kwargs):
        rep_extras = replace_unsats(extra_constraints)
        sat = super(CanonicalCacheMixin, self).satisfiable(extra_constraints=rep_extras,
                                                           **kwargs)
        if not sat and len(rep_extras) + len(self.constraints) > 0:
            ast = And(*(rep_extras + self.constraints))
            global_solution_cache.add_unsat(ast)

        return sat

    def solution(self, e, v, extra_constraints=(), **kwargs):
        rep_extras = replace_unsats(extra_constraints)
        if super(CanonicalCacheMixin, self).solution(e, v,
                                                     extra_constraints=rep_extras,
                                                     **kwargs):
            return True
        else:
            ast = And(*(rep_extras + self.constraints + [e == v,]))
            global_solution_cache.add_unsat(ast)
            return False

    def __getattr__(self, attr):
        if attr in ("eval", "batch_eval", "max", "min"):
            def handler(self, *args, **kwargs):
                if "extra_constraints" not in kwargs:
                    kwargs["extra_constraints"] = ()
                rep_extras = replace_unsats(kwargs["extra_constraints"])
                kwargs["extra_constraints"] = rep_extras
                try:
                    r = getattr(super(CanonicalCacheMixin, self), attr)(*args, **kwargs)
                    return r
                except UnsatError:
                    if len(rep_extras) + len(self.constraints) > 0:
                        ast = And(*(rep_extras + self.constraints))
                        global_solution_cache.add_unsat(ast)
                    raise
            return handler
        else:
            raise AttributeError(attr)
