from . import Backend
class BackendVariables(Backend):
    def __init__(self):
        Backend.__init__(self)
        self._op_expr['BVS'] = self.variables_yes
        self._op_expr['BoolS'] = self.variables_yes
        self._op_expr['FPS'] = self.variables_yes

        self._op_expr['BVV'] = self.variables_no
        self._op_expr['BoolV'] = self.variables_no
        self._op_expr['FPV'] = self.variables_no

    def _convert(self, a): #pylint:disable=unused-argument
        return frozenset()

    @staticmethod
    def variables_yes(s): #pylint:disable=unused-argument
        return frozenset((s.args[0],))

    @staticmethod
    def variables_no(s): #pylint:disable=unused-argument
        return frozenset()

    def _default_op(self, op, *args): #pylint:disable=unused-argument
        return frozenset.union(*args)

    def apply_annotation(self, s, a):
        if isinstance(a, VariableAnnotation):
            return s | a.extra_variables
        else:
            return s

from ..annotations import VariableAnnotation
