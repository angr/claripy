import logging
l = logging.getLogger("claripy.backends.backend_z3")

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
	def __init__(self):
		Backend.__init__(self)
		self._make_raw_ops(ops, op_module=z3)

	def process_args(self, args, exprs, model=None): #pylint:disable=W0613
		processed = [ ]
		for a in args:
			if type(a) is bv.BVV:
				processed.append(z3.BitVecVal(a.value, a.bits))
			elif type(a) in (int, long, float, str):
				processed.append(a)
			elif hasattr(a, '__module__') and a.__module__ == 'z3':
				processed.append(a)
			else:
				l.debug("BackendZ3 encountered unexpected type %s", type(a))
				raise BackendError("unexpected type %s encountered in BackendZ3", type(a))

		return processed

	def abstract(self, e):
		if e._obj.__module__ != 'z3':
			l.debug("unable to abstract non-Z3 object")
			raise BackendError("unable to abstract non-Z3 object")

		z = e._obj
		return self.abstract_z3(z, backends=e._backends)

	def abstract_z3(self, z, backends=None):
		children = [ self.abstract_z3(c) for c in z.children() ]
		name = z.decl().name()

		symbolic = any([ c.symbolic if isinstance(c, E) else False for c in children ])
		variables = set()
		for c in children:
			if isinstance(c, E):
				variables |= c.variables

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
			if name == 'extract':
				# GAH
				args = [ int(non_decimal.sub('', i)) for i in str(z).split(',')[:2] ] + children
			elif name in ('sign_extend', 'zero_extend'):
				args = int(str(z).split('(')[1].split(', ')[0]) + children
			elif name == 'zero_extend':
				args = int(str(z).split('(')[1].split(', ')[0]) + children
			else:
				if len(children) != 2 and not (name == 'bvnot' and len(children) == 1) and not (name == 'concat' and len(children) > 0):
					raise TypeError("%d children received for operation %s!" % (len(children), name))
				args = children
			op = function_map[name]

		return E(backends if backends is not None else [ self ], ast=A(op, args), variables=variables, symbolic=symbolic)

	def solver(self):
		return z3.Solver()

	def add_constraints(self, s, c):
		s.add(*c)

	def solve(self, s):
		if s.check() == z3.sat:
			satness = "sat"
			z3_model = s.model()
			model = { m.name(): z3_model.eval(m) for m in z3_model }
		else:
			satness = "unsat"
			model = None

		return Result(satness, model)

	def eval(self, s, expr, n, extra_constraints=None):
		expr_z3 = expr.eval(backends=[self])

		results = [ ]
		if extra_constraints is not None or n != 1:
			s.push()
		if extra_constraints is not None:
			s.add(*[e.eval(backends=[self]) for e in extra_constraints])

		for i in range(n):
			if s.check() == z3.sat:
				v = s.model().eval(expr_z3)
				results.append(E([self], symbolic=False, variables=set(), obj=v))
			else:
				break

			if i + 1 != n:
				s.add(expr_z3 != v)

		if extra_constraints is not None or n != 1:
			s.pop()

		if len(results) == 0:
			raise UnsatError("constraints are unsat")

		return results

	def min(self, s, expr, extra_constraints=None):
		expr_z3 = expr.eval(backends=[self])

		lo = 0
		hi = 2**expr_z3.size()-1

		numpop = 0
		if extra_constraints is not None:
			s.push()
			numpop += 1
			s.add(*[e.eval(backends=[self]) for e in extra_constraints])

		while hi-lo > 1:
			middle = (lo + hi)/2
			l.debug("h/m/l/d: %d %d %d %d", hi, middle, lo, hi-lo)

			s.push()
			s.add(self.call('UGE', (expr_z3, lo)), self.call('ULT', (expr_z3, middle)))
			numpop += 1

			if s.check() == z3.sat:
				 hi = middle - 1
			else:
				 lo = middle
				 s.constraints.pop()
				 numpop -= 1

			for _ in range(numpop):
				s.constraints.pop()

		if hi == lo: return lo
		else:
			s.push()
			s.add(expr_z3 == lo)
			if s.check() == z3.sat:
				s.pop()
				return lo
			else:
				s.pop()
		return hi

	def max(self, s, expr, extra_constraints=None):
		expr_z3 = expr.eval(backends=[self])

		lo = 0
		hi = 2**expr_z3.size()-1

		numpop = 0
		if extra_constraints is not None:
			s.push()
			numpop += 1
			s.add(*[e.eval(backends=[self]) for e in extra_constraints])

		while hi-lo > 1:
			middle = (lo + hi)/2
			l.debug("h/m/l/d: %d %d %d %d", hi, middle, lo, hi-lo)

			s.push()
			s.add(self.call('UGT', (expr_z3, middle)), self.call('ULE', (expr_z3, hi)))
			numpop += 1

			if s.check() == z3.sat:
				 lo = middle - 1
			else:
				 hi = middle
				 s.constraints.pop()
				 numpop -= 1

			for _ in range(numpop):
				s.constraints.pop()

		if hi == lo: return lo
		else:
			s.push()
			s.add(expr_z3 == hi)
			if s.check() == z3.sat:
				s.pop()
				return hi
			else:
				s.pop()
		return lo

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
function_map['bvuge'] = 'z3.UGE'
function_map['bvugt'] = 'z3.UGT'
function_map['bvule'] = 'z3.ULE'
function_map['bvult'] = 'z3.ULT'
function_map['concat'] = 'z3.Concat'
function_map['extract'] = 'z3.Extract'
function_map['or'] = 'z3.Or'
function_map['and'] = 'z3.And'
function_map['not'] = 'z3.Not'
function_map['if'] = 'z3.If'
function_map['bvlshr'] = 'z3.LShR'

from ..expression import E, A
from ..result import Result, UnsatError
