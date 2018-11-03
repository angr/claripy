import claripy
import networkx

from ..inversion import constraints_to_graph, get_descendents_and_inlaws, invert
from ..ast.base import Base, ASTCacheKey
from .full_frontend import FullFrontend


class KnotsFrontend(FullFrontend):
    def __init__(self, *args, **kwargs):
        super(KnotsFrontend, self).__init__(*args, **kwargs)
        self._graph = networkx.DiGraph()
        self._handlers = {}

        self._need_analysis = True
        self._special_replacements = None
        self._special_computations = None
        self._special_constraints = None

        for name in dir(self):
            if name.startswith('_handle_'):
                self._handlers[name[8:]] = getattr(self, name)

    #
    # Overridden methods
    #

    def add(self, constraints, invalidate_cache=True):
        if invalidate_cache:
            self._invalidate() # TODO: better than this
        # probably have a self.sensitive_values which triggers invalidation

        constraints = super(KnotsFrontend, self).add(constraints)
        queue = list(constraints)

        for constraint in constraints:
            self._graph.add_edge('ROOT', constraint.cache_key)

        while queue:
            el = queue.pop(0)
            if self._graph.succ[el.cache_key]:
                continue
            for i, arg in enumerate(el.args):
                if isinstance(arg, Base):
                    self._graph.add_edge(el.cache_key, arg.cache_key, arg_num=i)
                    queue.append(arg)
                else:
                    self._graph.add_edge(el.cache_key, arg, arg_num=i)

        return constraints

    def simplify(self):
        self._invalidate()
        return super(KnotsFrontend, self).simplify()

    def satisfiable(self, extra_constraints=(), exact=None):
        if extra_constraints != ():
            import ipdb; ipdb.set_trace() # can't deal with that shit yet

        return super(KnotsFrontend, self).satisfiable(extra_constraints=extra_constraints, exact=exact)

    def eval(self, expr, n, extra_constraints=(), exact=None):
        if extra_constraints != ():
            import ipdb; ipdb.set_trace() # can't deal with that shit yet

        if self._need_analysis:
            self._analyze_constraints()
        return super(KnotsFrontend, self).eval(expr.replace_dict(self.special_computations), n, extra_constraints=extra_constraints, exact=exact)

    def batch_eval(self, exprs, n, extra_constraints=(), exact=None):
        if extra_constraints != ():
            import ipdb; ipdb.set_trace() # can't deal with that shit yet

        if self._need_analysis:
            self._analyze_constraints()
        return super(KnotsFrontend, self).eval([expr.replace_dict(self.special_computations) for expr in exprs], n, extra_constraints=extra_constraints, exact=exact)

    def max(self, e, extra_constraints=(), exact=None):
        if extra_constraints != ():
            import ipdb; ipdb.set_trace() # can't deal with that shit yet

        return super(KnotsFrontend, self).max(e.replace_dict(self.special_computations), extra_constraints=extra_constraints, exact=exact)

    def min(self, e, extra_constraints=(), exact=None):
        if extra_constraints != ():
            import ipdb; ipdb.set_trace() # can't deal with that shit yet

        return super(KnotsFrontend, self).min(e.replace_dict(self.special_computations), extra_constraints=extra_constraints, exact=exact)

    def solution(self, e, v, extra_constraints=(), exact=None):
        if extra_constraints != ():
            import ipdb; ipdb.set_trace() # can't deal with that shit yet

        return super(KnotsFrontend, self).solution(e.replace_dict(self.special_computations), v, extra_constraints=extra_constraints, exact=exact)

    #
    # properties
    #

    @property
    def cool_constraints(self):
        if self._need_analysis:
            self._analyze_constraints()
        return [x.replace_dict(self.special_replacements) for x in self.constraints] + self.special_constraints

    @property
    def special_replacements(self):
        if self._need_analysis:
            self._analyze_constraints()
        return self._special_replacements

    @property
    def special_computations(self):
        if self._need_analysis:
            self._analyze_constraints()
        return self._special_computations

    @property
    def special_constraints(self):
        if self._need_analysis:
            self._analyze_constraints()
        return self._special_constraints

    #
    # analysis
    #

    def _invalidate(self):
        self._need_analysis = True

    def _add_constraints(self):
        self._solver_backend.add(self._tls.solver, self.cool_constraints, track=self._track)
        self._to_add = [ ]

    def _analyze_constraints(self):
        special_replacements = {}   # atoi(x) => tempvar
        special_computations = {}   # x => itoa(tempvar)
        special_constraints = []    # tempvar < 10000

        for nodekey in self._graph.nodes():
            if type(nodekey) is not ASTCacheKey or nodekey.ast.op not in self._handlers:
                continue

            rep, comp, con = self._handlers[nodekey.ast.op](nodekey.ast, allow_introspection=True)
            special_replacements[nodekey] = rep
            special_computations.update(comp)
            special_constraints.extend(con)

        self._special_computations = {k: self.naive_conversion(v) for k, v in special_computations.items()}
        self._special_replacements = special_replacements
        self._special_constraints = special_constraints
        self._need_analysis = False
        self._tls.solver = None

    def naive_conversion(self, ast):
        if not isinstance(ast, Base):
            return ast
        elif ast.op in self._handlers:
            return self._handlers[ast.op](ast, allow_introspection=False)[0]
        else:
            return type(ast)(ast.op, [self.naive_conversion(arg) for arg in ast.args])

    #
    # handlers
    #

    def _handle_Atoi(self, node, allow_introspection=True):
        if allow_introspection:
            _, inlaw = get_descendents_and_inlaws(self._graph, node.cache_key)
            can_invert = len(inlaw) == 0
        else:
            can_invert = False

        if can_invert:
            # nothing depends on any of the things this op depends on!
            # can be inverted and resolved later
            inversion = invert(node)
            return inversion.value, inversion.formulae, []
        else:
            # uh oh! gotta directly describe atoi
            chars = node.args[0].chop(8)
            size = node.args[1]
            char_assertion_fails = [claripy.Not(claripy.And(char >= b'0', char <= b'9')) for char in chars]

            cases = [self._atoi_success(chars[:i], size) for i, _ in enumerate(chars)]
            result = claripy.ite_cases(zip(char_assertion_fails, cases), self._atoi_success(chars, size))
            return result, {}, []

    def _handle_Itoa(self, node, allow_introspection=True):
        return claripy.Concat(*[0x30 + ((node.args[0] // 10**(node.args[1] - 1 - i)) % 10)[7:0] for i in range(node.args[1])]), {}, []

    @staticmethod
    def _atoi_success(chars, size):
        return sum(
                ((char - 0x30).zero_extend(size - 8) * 10**(len(chars) - 1 - i)
                    for i, char in enumerate(chars)),
                claripy.BVV(0, size))


