from .backend import Backend

class SolverBackend(Backend):
	def __init__(self, claripy):
		Backend.__init__(self, claripy)

	#
	# These functions provide solving and evaluation support.
	#

	def solver(self): #pylint:disable=W0613,R0201
		'''
		This function should return an instance of whatever object handles
		solving for this backend. For example, in Z3, this would be z3.Solver()
		'''
		raise NotImplementedError("backend doesn't support solving")

	def add_exprs(self, s, c):
		'''
		This function adds constraints to the backend solver.

		@param c: sequence of claripy.E objects
		@param s: backend solver object
		'''
		return self.add(s, self.convert_exprs(c))

	def add(self, s, c): #pylint:disable=W0613,R0201
		'''
		This function adds constraints to the backend solver.

		@param c: sequence of converted backend objects
		@param s: backend solver object
		'''
		raise NotImplementedError("backend doesn't support solving")

	def check_exprs(self, s, extra_constraints=None):
		'''
		This function does a constraint check.

		@params s: backend solver object
		@params extra_constraints: extra constraints (claripy.E objects) to add
								   to s for this solve
		@returns True or False, depending on satisfiability
		'''
		return self.check(s, extra_constraints=self.convert_exprs(extra_constraints))

	def check(self, s, extra_constraints=None): #pylint:disable=W0613,R0201
		'''
		This function does a constraint check.

		@params s: backend solver object
		@params extra_constraints: extra constraints (backend objects) to add
								   to s for this solve
		@returns True or False, depending on satisfiability
		'''
		raise NotImplementedError("backend doesn't support solving")

	def results_exprs(self, s, extra_constraints=None, generic_model=None):
		'''
		This function does a constraint check.

		@params s: backend solver object
		@params extra_constraints: extra constraints (claripy.E objects) to add to s for this solve
		@params generic_model: whether to generate a generic model in the Result object
		@returns a Result object
		'''
		return self.results(s, extra_constraints=self.convert_exprs(extra_constraints), generic_model=generic_model)

	def results(self, s, extra_constraints=None, generic_model=True): #pylint:disable=W0613,R0201
		'''
		This function does a constraint check.

		@params s: backend solver object
		@params extra_constraints: extra constraints (backend objects) to add to s for this solve
		@params generic_model: whether to generate a generic model in the Result object
		@returns a Result object
		'''
		raise NotImplementedError("backend doesn't support solving")

	def eval_expr(self, s, expr, n, extra_constraints=None, result=None):
		'''
		This function returns up to n possible solutions for expression expr.

		@params s: backend solver object
		@params expr: expression (claripy.E object) to evaluate
		@params n: number of results to return
		@params extra_constraints: extra constraints (claripy.E objects) to add to s for this solve
		@params result: a cached Result from the last constraint solve
		@returns a sequence of up to n results (backend objects)
		'''
		return self.eval(s, self.convert_expr(expr), n, extra_constraints=self.convert_exprs(extra_constraints), result=result)

	def eval(self, s, expr, n, extra_constraints=None, result=None): #pylint:disable=W0613,R0201
		'''
		This function returns up to n possible solutions for expression expr.

		@params s: backend solver object
		@params expr: expression (backend object) to evaluate
		@params n: number of results to return
		@params extra_constraints: extra constraints (backend objects) to add to s for this solve
		@params result: a cached Result from the last constraint solve
		@returns a sequence of up to n results (backend objects)
		'''
		raise NotImplementedError("backend doesn't support solving")

	def min_expr(self, s, expr, extra_constraints=None, result=None):
		'''
		Return the minimum value of expr.

		@params s: backend solver object
		@params expr: expression (claripy.E object) to evaluate
		@params extra_constraints: extra constraints (claripy.E objects) to add to s for this solve
		@params result: a cached Result from the last constraint solve
		@returns the minimum possible value of expr (backend object)
		'''
		return self.min(s, self.convert_expr(expr), extra_constraints=self.convert_exprs(extra_constraints), result=result)

	def min(self, s, expr, extra_constraints=None, result=None): #pylint:disable=W0613,R0201
		'''
		Return the minimum value of expr.

		@params s: backend solver object
		@params expr: expression (backend object) to evaluate
		@params extra_constraints: extra constraints (backend objects) to add to s for this solve
		@params result: a cached Result from the last constraint solve
		@returns the minimum possible value of expr (backend object)
		'''
		raise NotImplementedError("backend doesn't support solving")

	def max_expr(self, s, expr, extra_constraints=None, result=None):
		'''
		Return the maximum value of expr.

		@params s: backend solver object
		@params expr: expression (claripy.E object) to evaluate
		@params extra_constraints: extra constraints (claripy.E objects) to add to s for this solve
		@params result: a cached Result from the last constraint solve
		@returns the maximum possible value of expr (backend object)
		'''
		return self.max(s, self.convert_expr(expr), extra_constraints=self.convert_exprs(extra_constraints), result=result)

	def max(self, s, expr, extra_constraints=None, result=None): #pylint:disable=W0613,R0201
		'''
		Return the maximum value of expr.

		@params s: backend solver object
		@params expr: expression (backend object) to evaluate
		@params extra_constraints: extra constraints (backend objects) to add to s for this solve
		@params result: a cached Result from the last constraint solve
		@returns the maximum possible value of expr (backend object)
		'''
		raise NotImplementedError("backend doesn't support solving")

