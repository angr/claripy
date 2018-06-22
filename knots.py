import networkx
import claripy

class KnotFrontend(object):
    def __init__(self):
        self.constraints = []
        self._graph = None
        self._handlers = {}

        for name in dir(self):
            if name.startswith('_handle_'):
                self._handlers[name[8:]] = getattr(self, name)

    def add(self, constraint):
        self.constraints.append(constraint)

    def eval(self, expr, n):
        self._graph = constraints_to_graph(self.constraints)

        special_replacements = {}   # atoi(x) => tempvar
        special_computations = {}   # x => itoa(tempvar)
        special_constraints = []    # tempvar < 10000

        for nodekey in self._graph.nodes():
            if type(nodekey) is not claripy.ASTCacheKey or nodekey.ast.op not in self._handlers:
                continue

            rep, comp, con = self._handlers[nodekey.ast.op](nodekey.ast, allow_introspection=True)
            special_replacements[nodekey] = rep
            special_computations.update(comp)
            special_constraints.extend(con)

        special_computations = {k: self.naive_conversion(v) for k, v in special_computations.iteritems()}

        solver = claripy.Solver()
        for con in self.constraints:
            solver.add(con.replace_dict(special_replacements))
        return solver.eval(expr.replace_dict(special_computations), n)

    def naive_conversion(self, ast):
        if not isinstance(ast, claripy.ast.Base):
            return ast
        elif ast.op in self._handlers:
            return self._handlers[ast.op](ast, allow_introspection=False)
        else:
            return type(ast)(ast.op, [self.naive_conversion(arg) for arg in ast.args])

    def _handle_Atoi(self, node, allow_introspection=True):
        if allow_introspection:
            _, inlaw = get_descendents_and_inlaws(self._graph, node.cache_key)
        else:
            inlaw = ()

        if len(inlaw) == 0:
            # nothing depends on any of the things this op depends on!
            # can be inverted and resolved later
            inversion = claripy.invert(node)
            return inversion.value, inversion.formulae, []
        else:
            # uh oh! gotta directly describe atoi
            chars = node.args[0].chop(8)
            size = node.args[1]
            char_assertion_fails = [claripy.Not(claripy.And(char >= '0', char <= '9')) for char in chars]

            cases = [self._atoi_success(chars[:i], size) for i, _ in enumerate(chars)]
            result = claripy.ite_cases(zip(char_assertion_fails, cases), self._atoi_success(chars, size))
            return result, {}, []

    def _handle_Itoa(self, node, allow_introspection=True):
        return claripy.Concat(*[0x30 + ((node.args[0] // 10**(node.args[1] - 1 - i)) % 10)[7:0] for i in xrange(node.args[1])])

    @staticmethod
    def _atoi_success(chars, size):
        return sum(
                ((char - '0').zero_extend(size - 8) * 10**(len(chars) - 1 - i)
                    for i, char in enumerate(chars)),
                claripy.BVV(0, size))


def constraints_to_graph(constraints):
    ckeys = [ast.cache_key for ast in constraints]
    seen = set(ckeys)
    queue = list(ckeys)
    graph = networkx.DiGraph()

    for ast_key in ckeys:
        graph.add_edge('ROOT', ast_key)

    while queue:
        ast_key = queue.pop(0)
        for i, arg in enumerate(ast_key.ast.args):
            if isinstance(arg, claripy.ast.Base):
                arg = arg.cache_key
                graph.add_edge(ast_key, arg, arg_num=i)
                if arg not in seen:
                    seen.add(arg)
                    queue.append(arg)
            else:
                graph.add_edge(ast_key, arg, arg_num=i)

    return graph

def get_descendents_and_inlaws(graph, root):
    seen = set([root])
    unseen = set()
    queue = [root]
    while queue:
        node = queue.pop(0)
        for arg in node.ast.args:
            if not isinstance(arg, claripy.ast.Base):
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

if __name__ == '__main__':
    s = KnotFrontend()
    input_string = claripy.BVS('input', 30*8)
    atoi_of_that = claripy.Atoi(input_string, 32)
    s.add(atoi_of_that * 20 > 300)
    s.add(atoi_of_that * 20 < 400)
    s.add(atoi_of_that < 10000)
    #s.add(input_string.chop(8)[-2] == '1')
    for val in s.eval(input_string, 5):
        print repr(hex(val)[2:].strip('L').rjust(len(input_string)//4, '0').decode('hex'))
