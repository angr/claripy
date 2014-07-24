import logging
l = logging.getLogger("claripy.backends.backend_z3")

solve_count = 0
cache_count = 0

# import and set up Z3
import os
import z3
if "Z3PATH" in os.environ:
	z3_path = os.environ["Z3PATH"]
elif "VIRTUAL_ENV" in os.environ:
	virtual_env = os.environ["VIRTUAL_ENV"]
	z3_path = virtual_env + "/lib/"
else:
	z3_path = "/opt/python/lib/"
z3.init(z3_path + "libz3.so")

from .backend import Backend, BackendError, ops
from .. import bv

class BackendZ3(Backend):
	_split_on = { 'And', 'Or' }

	def __init__(self, claripy):
		Backend.__init__(self, claripy)
		self._make_raw_ops(ops, op_module=z3)
		self._op_expr['BitVec'] = self.BitVec

	def BitVec(self, name, size, model=None):
		if model and name in model:
			return self.wrap(model[name], variables=set(), symbolic=False)
		else:
			return self.wrap(z3.BitVec(name, size), variables={name}, symbolic=True)

	def convert(self, obj, model=None):
		if type(obj) is bv.BVV:
			return z3.BitVecVal(obj.value, obj.bits)
		elif type(obj) in (int, long, bool, float, str):
			return obj
		elif hasattr(obj, '__module__') and obj.__module__ == 'z3':
			return obj
		else:
			l.debug("BackendZ3 encountered unexpected type %s", type(obj))
			raise BackendError("unexpected type %s encountered in BackendZ3", type(obj))


	def convert_expr(self, a, model=None): #pylint:disable=W0613
		if isinstance(a, E): obj = a.eval(backends=[self])
		else: obj = a
		return self.convert(obj, model=model)

	def abstract(self, e, split_on=None):
		if not hasattr(e._obj, '__module__') or e._obj.__module__ != 'z3':
			l.debug("unable to abstract non-Z3 object")
			raise BackendError("unable to abstract non-Z3 object")

		z = e._obj
		s, v, a = self.abstract_z3(z, self._split_on if split_on is None else split_on)
		return E(self._claripy, symbolic=s, variables=v, ast=a)

	def abstract_z3(self, z, split_on):
		name = z.decl().name()
		new_split_on = split_on if name in function_map and function_map[name] in split_on else set()
		children = [ self.abstract_z3(c, new_split_on) for c in z.children() ]

		symbolic = False
		variables = set()

		if len(children) == 0:
			if z.__class__ == z3.BitVecRef:
				op = "BitVec"
				args = (name, z.size())
				symbolic = True
				variables = { name }
			elif z.__class__ == z3.BitVecNumRef:
				op = "BitVecVal"
				args = (z.as_long(), z.size())
			elif name == 'true':
				op = "BoolVal"
				args = (True,)
			elif name == 'false':
				op = "BoolVal"
				args = (False,)
			else:
				raise TypeError("Unable to wrap type %s", z.__class__.__name__)
		else:
			raw_args = [ ]
			for s, v, a in children:
				if function_map[name] in split_on:
					raw_args.append(E(self._claripy, ast=a, variables=v, symbolic=s))
				else:
					raw_args.append(a)
				symbolic |= s
				variables |= v

			if name == 'extract':
				# GAH
				args = [ int(non_decimal.sub('', i)) for i in str(z).split(',')[:2] ] + raw_args
			elif name in ('sign_extend', 'zero_extend'):
				args = int(str(z).split('(')[1].split(', ')[0]) + raw_args
			elif name == 'zero_extend':
				args = int(str(z).split('(')[1].split(', ')[0]) + raw_args
			else:
				args = raw_args
			op = function_map[name]

		return symbolic, variables, A(op, args)

	def solver(self):
		return z3.Solver()

	def add(self, s, c):
		s.add(*c)

	def check(self, s, extra_constraints=None): #pylint:disable=R0201
		global solve_count
		solve_count += 1
		if extra_constraints is not None:
			s.push()
			s.add(*extra_constraints)

		satness = s.check() == z3.sat

		if extra_constraints is not None:
			s.pop()
		return satness

	def results(self, s, extra_constraints=None, generic_model=True):
		satness = self.check(s, extra_constraints=extra_constraints)
		model = None
		z3_model = None

		if satness:
			l.debug("sat!")
			z3_model = s.model()
			l.debug("model is %r", z3_model)
			if generic_model:
				model = { }
				for m_f in z3_model:
					n = m_f.name()
					m = m_f()
					model[n] = z3_model.eval(m)
		else:
			l.debug("unsat!")

		return Result(satness, model, backend_model=z3_model)

	def eval(self, s, expr, n, extra_constraints=None, model=None):
		global solve_count, cache_count

		#if n == 1 and model is None:
		#	import ipdb; ipdb.set_trace()

		results = [ ]
		if extra_constraints is not None or n != 1:
			s.push()
		if extra_constraints is not None:
			s.add(*[self.convert_expr(e) for e in extra_constraints])
			model = None

		for i in range(n):
			if model is None:
				solve_count += 1
				if s.check() == z3.sat:
					model = s.model()
			else:
				cache_count += 1

			if model is None:
				break

			if not type(expr) in { int, float, str, bool, long }:
				v = model.eval(expr, model_completion=True)
			else:
				v = expr

			results.append(v)
			if i + 1 != n:
				s.add(expr != v)
				model = None

		if extra_constraints is not None or n != 1:
			s.pop()

		if len(results) == 0:
			raise UnsatError("constraints are unsat")

		return results

	def min(self, s, expr, extra_constraints=None, model=None): #pylint:disable=W0613
		global solve_count

		lo = 0
		hi = 2**expr.size()-1

		numpop = 0
		if extra_constraints is not None:
			s.push()
			numpop += 1
			s.add(*[self.convert_expr(e) for e in extra_constraints])

		while hi-lo > 1:
			middle = (lo + hi)/2
			l.debug("h/m/l/d: %d %d %d %d", hi, middle, lo, hi-lo)

			s.push()
			s.add(z3.UGE(expr, lo), z3.ULE(expr, middle))
			numpop += 1

			solve_count += 1
			if s.check() == z3.sat:
				l.debug("... still sat")
				hi = middle
			else:
				l.debug("... now unsat")
				lo = middle
				s.pop()
				numpop -= 1

		for _ in range(numpop):
			s.pop()

		l.debug("final hi/lo: %d, %d", hi, lo)

		if hi == lo: return lo
		else:
			s.push()
			s.add(expr == lo)
			if s.check() == z3.sat:
				s.pop()
				return lo
			else:
				s.pop()
		return hi

	def max(self, s, expr, extra_constraints=None, model=None): #pylint:disable=W0613
		global solve_count

		lo = 0
		hi = 2**expr.size()-1

		numpop = 0
		if extra_constraints is not None:
			s.push()
			numpop += 1
			s.add(*[self.convert_expr(e) for e in extra_constraints])

		while hi-lo > 1:
			middle = (lo + hi)/2
			l.debug("h/m/l/d: %d %d %d %d", hi, middle, lo, hi-lo)

			s.push()
			s.add(z3.UGT(expr, middle), z3.ULE(expr, hi))
			numpop += 1

			solve_count += 1
			if s.check() == z3.sat:
				l.debug("... still sat")
				lo = middle
			else:
				l.debug("... now unsat")
				hi = middle
				s.pop()
				numpop -= 1
			l.debug("    now: %d %d %d %d", hi, middle, lo, hi-lo)

		for _ in range(numpop):
			s.pop()

		if hi == lo: return lo
		else:
			s.push()
			s.add(expr == hi)
			if s.check() == z3.sat:
				s.pop()
				return hi
			else:
				s.pop()
		return lo

	def simplify(self, expr): #pylint:disable=W0613,R0201
		raise Exception("This shouldn't be called. But Yan.")

	def simplify_expr(self, expr):
		l.debug("SIMPLIFYING EXPRESSION")

		expr_raw = self.convert_expr(expr)
		symbolic = expr.symbolic
		variables = expr.variables

		l.debug("... before: %s", expr_raw)

		if isinstance(expr_raw, z3.BoolRef):
			tactics = z3.Then(z3.Tactic("simplify"), z3.Tactic("propagate-ineqs"), z3.Tactic("propagate-values"), z3.Tactic("unit-subsume-simplify"))
			s = tactics(expr_raw).as_expr()

			if s.sexpr() == 'true':
				s = True
				symbolic = False
				variables = set()
			elif s.sexpr() == 'false':
				s = False
				symbolic = False
				variables = set()
		elif isinstance(expr_raw, z3.BitVecRef):
			s = z3.simplify(expr_raw)
			symbolic = not isinstance(expr, z3.BitVecNumRef)
			if not symbolic:
				variables = set()

			#import ipdb; ipdb.set_trace()
		else:
			s = expr_raw

		l.debug("... after: %s", s)

		return self.wrap(s, symbolic=symbolic, variables=variables)

#
# this is for the actual->abstract conversion above
#

import re
non_decimal = re.compile(r'[^\d.]+')

function_map = { }
function_map['bvadd'] = '__add__'
function_map['bvxor'] = '__and__'
function_map['bvsdiv'] = '__div__'
function_map['bvsdiv_i'] = '__div__' # TODO: make sure this is correct
function_map['bvnot'] = '__invert__'
function_map['bvshl'] = '__lshift__'
function_map['bvsmod'] = '__mod__'
function_map['bvmul'] = '__mul__'
function_map['distinct'] = '__ne__'
function_map['bvneg'] = '__neg__'
function_map['bvor'] = '__or__'
function_map['bvashr'] = '__rshift__'
function_map['bvsub'] = '__sub__'
function_map['bvxor'] = '__xor__'
function_map['='] = '__eq__'
function_map['bvsgt'] = '__gt__'
function_map['bvsge'] = '__ge__'
function_map['bvslt'] = '__lt__'
function_map['bvsle'] = '__le__'
function_map['bvuge'] = 'UGE'
function_map['bvugt'] = 'UGT'
function_map['bvule'] = 'ULE'
function_map['bvult'] = 'ULT'
function_map['concat'] = 'Concat'
function_map['extract'] = 'Extract'
function_map['or'] = 'Or'
function_map['and'] = 'And'
function_map['not'] = 'Not'
function_map['if'] = 'If'
function_map['bvlshr'] = 'LShR'

from ..expression import E, A
from ..result import Result, UnsatError
