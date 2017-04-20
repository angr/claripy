from . import Backend
class BackendITEExcavator(Backend):
    def __init__(self):
        Backend.__init__(self)
        for o in operations.leaf_operations:
            self._op_expr[o] = self._convert

        self._op_raw['If'] = self.if_handler

    # if we are an If, call the If handler so that we can take advantage of its simplifiers
    @staticmethod
    def if_handler(c, t, f):
        return get_structure('If', (c, t, f))._simplify()

    def _default_op(self, op, *excavated_args):
        ite_args = [ isinstance(a, ASTStructure) and a.op == 'If' for a in excavated_args ]

        if ite_args.count(True) == 0:
            # if there are no ifs that came to the surface, there's nothing more to do
            return get_structure(op, excavated_args)
        else:
            # this gets called when we're *not* in an If, but there are Ifs in the args.
            # it pulls those Ifs out to the surface.
            cond = excavated_args[ite_args.index(True)].args[0]
            new_true_args = [ ]
            new_false_args = [ ]

            for a in excavated_args:
                #print "OC", cond.dbg_repr()
                #print "NC", Not(cond).dbg_repr()

                if not isinstance(a, ASTStructure) or a.op != 'If':
                    new_true_args.append(a)
                    new_false_args.append(a)
                elif a.args[0] is cond:
                    #print "AC", a.args[0].dbg_repr()
                    new_true_args.append(a.args[1])
                    new_false_args.append(a.args[2])
                elif a.args[0] is get_structure('Not', (cond,))._simplify():
                    #print "AN", a.args[0].dbg_repr()
                    new_true_args.append(a.args[2])
                    new_false_args.append(a.args[1])
                else:
                    #print "AB", a.args[0].dbg_repr()
                    # weird conditions -- giving up!
                    return get_structure(op, excavated_args)

            return get_structure('If', (cond, get_structure(op, new_true_args), get_structure(op, new_false_args)))

from ..ast.structure import ASTStructure, get_structure
from .. import operations
