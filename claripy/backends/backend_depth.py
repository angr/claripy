from . import Backend
class BackendDepth(Backend):
    def __init__(self):
        Backend.__init__(self)
        self._op_expr['BVS'] = self.depth_zero
        self._op_expr['BVV'] = self.depth_zero
        self._op_expr['BoolV'] = self.depth_zero
        self._op_expr['BoolS'] = self.depth_zero
        self._op_expr['FPV'] = self.depth_zero
        self._op_expr['FPS'] = self.depth_zero

    def _convert(self, a): #pylint:disable=unused-argument
        return 0

    def _default_op(self, op, *args): #pylint:disable=unused-argument
        return max(args) + 1

    @staticmethod
    def depth_zero(a): #pylint:disable=unused-argument
        return 1
