import networkx

from .ast.bv import BVS, BVV, Concat, Itoa
from .ast.base import Base

class Inversion(object):
    def __init__(self, value, formulae):
        self.value = value
        self.formulae = formulae

    @property
    def live(self):
        return self.value.op == 'BVS'

    def apply(self, temp, value, replacement):
        formulae = {k: v.replace(value, replacement) for k, v in self.formulae.items()}
        if not is_temp(value):
            formulae[value.cache_key] = replacement
        return Inversion(temp, formulae)

def make_temp(size):
    return BVS('invertemp', size)

def is_temp(v):
    return v.op == 'BVS' and v.args[0].startswith('invertemp')

def invert(ast):
    """
    "inversion" is a mechanism for describing how to compute the inputs of an expression given the outputs.

    Given an AST, if possible, return a temporary BVS and a mapping from each of the leaf BVSs in the original AST to an AST computing a value with the temp at the leaves.

    :param ast:     A claripy expression to invert
    :return:        An "Inversion" object, which contains a ``.value`` of the same type as `ast` and ` ``.formulae`` mapping leaves of `ast` to computations from ``.value``.
    """
    if type(ast) in (int, str, bytes):
        return Inversion(ast, {})
    if ast.op in ('BVV', 'BVS'):
        return Inversion(ast, {})

    sz = len(ast)
    iargs = list(map(invert, ast.args))
    result_formulae, wash = formulae_union(iargs)

    if wash:
        pass

    elif ast.op == 'Concat':
        if all(c.live for c in iargs):
            t = make_temp(sz)
            r = Inversion(t, result_formulae)
            sofar = 0
            for c in iargs:
                if c.value.cache_key in r.formulae:
                    wash = True
                    break
                r = r.apply(t, c.value, t[sz - sofar + 1: sz - sofar + len(c.value)])
            else:
                return r

    elif ast.op == 'Extract':
        c = iargs[2]
        if c.live:
            t = make_temp(sz)
            return c.apply(t, c.value, Concat(BVV(0, len(c.value) - ast.args[0] - 1), t, BVV(0, ast.args[1])))

    elif ast.op == 'Atoi':
        c = iargs[0]
        if c.live:
            t = make_temp(sz)
            return c.apply(t, c.value, Itoa(t, len(ast.args[0]) // 8))

    #elif ast.op == '__add__':
    #    if len([c for c in iargs l # ?????????????????????????

    if wash:
        return Inversion(ast, result_formulae)
    else:
        return Inversion(type(ast)(ast.op, [inv.value for inv in iargs]), result_formulae)

def formulae_union(iargs):
    result_formulae = {}
    wash = False

    for iarg in iargs:
        for k in iarg.formulae:
            if wash:
                result_formulae[k] = None
            else:
                if k in result_formulae:
                    wash = True
                    for k2 in result_formulae:
                        result_formulae[k2] = None
                    result_formulae[k] = None
                else:
                    result_formulae[k] = iarg.formulae[k]
    return result_formulae, wash

def constraints_to_graph(constraints):
    """
    Convert some constraints to a graph of edges between values.

    :param constraints:     A list of constraints
    :return:                A digraph, with each operation as a node and each argument as an edge from the op to the arg.
                            All initial constraints will be linked to a root element which is just the string "ROOT".
                            All non-AST elements will just appear in the graph directly.
    """
    ckeys = [ast.cache_key for ast in constraints]
    seen = set(ckeys)
    queue = list(ckeys)
    graph = networkx.DiGraph()

    for ast_key in ckeys:
        graph.add_edge('ROOT', ast_key)

    while queue:
        ast_key = queue.pop(0)
        for i, arg in enumerate(ast_key.ast.args):
            if isinstance(arg, Base):
                arg = arg.cache_key
                graph.add_edge(ast_key, arg, arg_num=i)
                if arg not in seen:
                    seen.add(arg)
                    queue.append(arg)
            else:
                graph.add_edge(ast_key, arg, arg_num=i)

    return graph

def get_descendents_and_inlaws(graph, root):
    """
    Find the elements of a constraint graph that are descendants of a root node, and the nodes that
    connect to any of the descendants without being descendant themselves (inlaws).

    :param graph:   A constraint graph, as per constraints_to_graph.
    :param root:    A member of the constraint graph.
    :return:        A tuple of (descendants, inlaws)
    """
    seen = {root}
    unseen = set()
    queue = [root]
    while queue:
        node = queue.pop(0)
        for arg in node.ast.args:
            if not isinstance(arg, Base):
                continue
            arg = arg.cache_key
            if arg in seen:
                continue
            seen.add(arg)
            queue.append(arg)

            if arg in unseen:
                unseen.remove(arg)
            for parent in graph.pred[arg]:
                if parent not in seen:
                    unseen.add(parent)

    return seen, unseen

