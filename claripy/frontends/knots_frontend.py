import claripy
import networkx
from typing import Dict, Set, List
from contextlib import contextmanager

from ..inversion import constraints_to_graph, get_descendents_and_inlaws, invert
from ..ast.base import Base, ASTCacheKey
from ..ast.bool import Bool
from .full_frontend import FullFrontend


class KnotsFrontend(FullFrontend):
    def __init__(self, *args, **kwargs):
        super(KnotsFrontend, self).__init__(*args, **kwargs)
        self._graph = networkx.DiGraph()
        self._handlers = {}

        self._need_analysis = True

        # atoi(x) => tempvar
        self._special_replacements = None # type: Dict[ASTCacheKey, Base]
        # x => itoa(tempvar)
        self._special_computations = None # type: Dict[ASTCacheKey, Base]
        # tempvar < 10000
        self._special_constraints = None  # type: List[Bool]
        # any variable for which constraining it should trigger analysis
        self._special_variables = None    # type: Set[str]

        for name in dir(self):
            if name.startswith('_handle_'):
                self._handlers[name[8:]] = getattr(self, name)

    #
    # Overridden methods
    #

    def add(self, constraints: List[Bool], invalidate_cache=True):
        # check to see if we need to invalidate the analysis
        # we trust anyone who sets invalidate_cache=False
        # (we can also opt out if self._special_variables is None bc there's nothing to invalidate)
        if invalidate_cache and self._special_variables is not None and (constraint.variables.intersection(self._special_variables) for constraint in constraints):
            self._invalidate()

        # super-call. self.constraints should appear to maintain its normal behavior w.r.t.
        # the client adding constraints and them appearing there
        constraints = super(KnotsFrontend, self).add(constraints)

        # the remainder of this method is about updating the constraint graph
        for constraint in constraints:
            self._graph.add_edge('ROOT', constraint.cache_key)

        queue = list(constraints)
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
        with self._sanitize_extra_constraints(extra_constraints) as ec:
            return super(KnotsFrontend, self).satisfiable(extra_constraints=ec, exact=exact)

    def eval(self, expr, n, extra_constraints=(), exact=None):
        with self._sanitize_extra_constraints(extra_constraints) as ec:
            return super(KnotsFrontend, self).eval(self._sanitize_expr(expr), n, extra_constraints=ec, exact=exact)

    def batch_eval(self, exprs, n, extra_constraints=(), exact=None):
        with self._sanitize_extra_constraints(extra_constraints) as ec:
            return super(KnotsFrontend, self).eval([self._sanitize_expr(expr) for expr in exprs], n, extra_constraints=ec, exact=exact)

    # TODO: think this through: do we need to contort ourselves to be okay with the implicit constraints added while narrowing down max/min?
    def max(self, e, extra_constraints=(), exact=None):
        with self._sanitize_extra_constraints(extra_constraints) as ec:
            return super(KnotsFrontend, self).max(self._sanitize_expr(e), extra_constraints=ec, exact=exact)

    def min(self, e, extra_constraints=(), exact=None):
        with self._sanitize_extra_constraints(extra_constraints) as ec:
            return super(KnotsFrontend, self).min(self._sanitize_expr(e), extra_constraints=ec, exact=exact)

    def solution(self, e, v, extra_constraints=(), exact=None):
        with self._sanitize_extra_constraints(extra_constraints) as ec:
            return super(KnotsFrontend, self).solution(self._sanitize_expr(e), v, extra_constraints=ec, exact=exact)

    # here's the magic! this is the method called to put the constraints into the solver
    # so by overriding it we can use only our translated constraints.
    def _add_constraints(self):
        self._solver_backend.add(self._tls.solver, self.translated_constraints, track=self._track)
        self._to_add = [ ]

    #
    # properties
    #

    @property
    def translated_constraints(self):
        """
        The constraints which will actually be fed to the solver
        """
        if self._need_analysis:
            self._analyze_constraints()
        return [x.replace_dict(self.special_replacements) for x in self.constraints] + self.special_constraints

    @property
    def special_replacements(self):
        """
        A mapping from knot-y expression to simple expression
        """
        if self._need_analysis:
            self._analyze_constraints()
        return self._special_replacements

    @property
    def special_computations(self):
        """
        A mapping from the leaves of any knot-y expressions to how they can be computed from the
        leaves of the simple expressions in `special_replacements`
        """
        if self._need_analysis:
            self._analyze_constraints()
        return self._special_computations

    @property
    def special_constraints(self):
        """
        Any extra constraints that fell out of the replacement analysis
        """
        if self._need_analysis:
            self._analyze_constraints()
        return self._special_constraints

    @property
    def special_variables(self):
        """
        Any variables for which constraining them further should trigger re-analysis
        """
        if self._need_analysis:
            self._analyze_constraints()
        return self._special_variables

    #
    # analysis
    #

    def _invalidate(self):
        self._need_analysis = True

    def _analyze_constraints(self):
        special_replacements = {}
        special_computations = {}
        special_constraints = []
        special_variables = set()

        for nodekey in self._graph.nodes():
            if type(nodekey) is not ASTCacheKey or nodekey.ast.op not in self._handlers:
                continue

            rep, comp, con = self._handlers[nodekey.ast.op](nodekey.ast, allow_introspection=True)
            special_replacements[nodekey] = rep
            special_computations.update(comp)
            special_constraints.extend(con)
            special_variables.update(var.ast.variables for var in comp.keys())

        self._special_computations = {k: self.naive_conversion(v) for k, v in special_computations.items()}
        self._special_replacements = special_replacements
        self._special_constraints = special_constraints
        self._special_variables = special_variables
        self._need_analysis = False
        self._tls.solver = None

    def naive_conversion(self, ast: Base):
        if not isinstance(ast, Base):
            return ast
        elif ast.op in self._handlers:
            # TODO: this ought to recurse on the resulting arguments as well
            return self._handlers[ast.op](ast, allow_introspection=False)[0]
        else:
            return type(ast)(ast.op, [self.naive_conversion(arg) for arg in ast.args])

    def _sanitize_expr(self, ast: Base):
        # TODO: run this through naive_conversion in case the client passes in an unknown knot
        # TODO: this is. a lot of AST traffic. should we do a custom replace method?
        # This substitution is extremely fragile. what's the deal?
        # DON'T FORGET: replace_dict will use the dict you pass it as the cache!
        return ast.replace_dict(self.special_replacements).replace_dict(self.special_computations)

    @contextmanager
    def _sanitize_extra_constraints(self, extra: List[Bool]):
        # we do NOT want to use _sanitize_expr since we do NOT want to use special_computations
        # since that will replace the special variables and we want to be on the lookout for those.
        # however we should be mindful of what happens if the client passes an unknown knot
        extra = [con.replace_dict(self.special_replacements) for con in extra]

        if not any(c.variables.intersection(self.special_variables) for c in extra):
            # easy case. phew.
            yield extra
            return

        import ipdb; ipdb.set_trace()
        # aw, *hell* no
        self._tls.solver = self._solver_backend.solver(timeout=self.timeout)
        # something something
        # we somehow need to run the analysis while taking into account extra constraints
        # but also separate the extra constraints from the real constraints bc there's lots of weird
        # caching behavior when extra constraints are empty?
        yield []
        self._tls.solver = None

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


