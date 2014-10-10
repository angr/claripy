from .backend import Backend

class ModelBackend(Backend):
	'''
	A ModelBackend is a backend that does not support solving (and, thus,
	constraints), but still supports max(), min(), eval(), etc.
	'''

	def __init__(self):
		Backend.__init__(self)

	#
	# These functions provide solving and evaluation support.
	#

	def eval_expr(self, expr, n, result=None):
		'''
		This function returns up to n possible solutions for expression expr.

		@param expr: expression (claripy.E object) to evaluate
		@param n: number of results to return
		@param result: a cached Result from the last constraint solve
		@returns a sequence of up to n results (backend objects)
		'''
		return self.eval(self.convert_expr(expr), n, result=result)

	def eval(self, expr, n, result=None): #pylint:disable=unused-argument,no-self-use
		'''
		This function returns up to n possible solutions for expression expr.

		@param expr: expression (backend object) to evaluate
		@param n: number of results to return
		@param result: a cached Result from the last constraint solve
		@returns a sequence of up to n results (backend objects)
		'''
		raise BackendError("backend doesn't support eval()")

	def min_expr(self, expr, result=None):
		'''
		Return the minimum value of expr.

		@param expr: expression (claripy.E object) to evaluate
		@param result: a cached Result from the last constraint solve
		@returns the minimum possible value of expr (backend object)
		'''
		return self.min(self.convert_expr(expr), result=result)

	def min(self, expr, result=None): #pylint:disable=unused-argument,no-self-use
		'''
		Return the minimum value of expr.

		@param expr: expression (backend object) to evaluate
		@param result: a cached Result from the last constraint solve
		@returns the minimum possible value of expr (backend object)
		'''
		raise BackendError("backend doesn't support min()")

	def max_expr(self, expr, result=None):
		'''
		Return the maximum value of expr.

		@param expr: expression (claripy.E object) to evaluate
		@param result: a cached Result from the last constraint solve
		@returns the maximum possible value of expr (backend object)
		'''
		return self.max(self.convert_expr(expr), result=result)

	def max(self, expr, result=None): #pylint:disable=unused-argument,no-self-use
		'''
		Return the maximum value of expr.

		@param expr: expression (backend object) to evaluate
		@param result: a cached Result from the last constraint solve
		@returns the maximum possible value of expr (backend object)
		'''
		raise BackendError("backend doesn't support max()")

	def solution_expr(self, expr, v, result=None):
		'''
		Return True if v is a solution of expr with the extra constraints, False otherwise.

		@param expr: expression (claripy.E) to evaluate
		@param v: the proposed solution (claripy.E)
		@param result: a cached Result from the last constraint solve
		@returns True if v is a solution of expr, False otherwise
		'''

		return self.solution(self.convert_expr(expr), self.convert_expr(v), result=result)

	def solution(self, expr, v, result=None): #pylint:disable=unused-argument,no-self-use
		'''
		Return True if v is a solution of expr with the extra constraints, False otherwise.

		@param expr: expression (backend object) to evaluate
		@param v: the proposed solution (backend object)
		@param result: a cached Result from the last constraint solve
		@returns True if v is a solution of expr, False otherwise
		'''

		raise BackendError("backend doesn't support solution()")

	def has_false(self, o):
		return o == False

	def has_true(self, o):
		return o == True

	def is_false(self, o):
		return o == False

	def is_true(self, o):
		return o == True

from ..errors import BackendError
