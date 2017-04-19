from . import Backend
class BackendSymbolic(Backend):
	def __init__(self):
		Backend.__init__(self)
		self._op_expr['BVS'] = self.symbolic_yes
		self._op_expr['BoolS'] = self.symbolic_yes
		self._op_expr['FPS'] = self.symbolic_yes
		self._op_expr['BVV'] = self.symbolic_no
		self._op_expr['BoolV'] = self.symbolic_no
		self._op_expr['FPV'] = self.symbolic_no

	def _convert(self, a): #pylint:disable=unused-argument
		return False

	@staticmethod
	def symbolic_yes(s): #pylint:disable=unused-argument
		return True

	@staticmethod
	def symbolic_no(s): #pylint:disable=unused-argument
		return False

	@staticmethod
	def symbolic_any(s): #pylint:disable=unused-argument
		return False

	def _default_op(self, op, *args): #pylint:disable=unused-argument
		return any(args)
