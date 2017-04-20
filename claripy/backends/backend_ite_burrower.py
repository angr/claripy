from . import Backend
class BackendITEBurrower(Backend):
    def __init__(self):
        Backend.__init__(self)
        for o in operations.leaf_operations:
            self._op_expr[o] = self._convert

        self._op_expr['If'] = self.if_handler

    def _default_op(self, op, *args):
        return get_structure(op, args)

    def if_handler(self, expr):
        if not all(isinstance(a, ASTStructure) for a in expr.args):
            #print "not all my args are bases"
            return expr

        old_true = expr.args[1]
        old_false = expr.args[2]

        if old_true.op != old_false.op or len(old_true.args) != len(old_false.args):
            return expr

        if old_true.op == 'If':
            # let's no go into this right now
            return expr

        if any(a.op in operations.leaf_operations for a in expr.args):
            # burrowing through these is pretty funny
            return expr

        matches = [ old_true.args[i] == old_false.args[i] for i in range(len(old_true.args)) ]
        if matches.count(False) != 1 or all(matches):
            # TODO: handle multiple differences for multi-arg ast nodes
            #print "wrong number of matches:",matches,old_true,old_false
            return expr

        different_idx = matches.index(False)
        inner_if = expr.swap_args((expr.args[0], old_true.args[different_idx], old_false.args[different_idx]))
        new_args = list(old_true.args)
        new_args[different_idx] = self.convert(inner_if)
        #print "replaced the",different_idx,"arg:",new_args
        return old_true.swap_args(new_args)

from ..ast.structure import ASTStructure, get_structure
from .. import operations
