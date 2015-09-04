import sys
import logging
l = logging.getLogger("claripy.backends.backend_z3")

if sys.platform == 'darwin':
    z3_library_file = "libz3.dylib"
elif sys.platform == 'win32':
    z3_library_file = "libz3.dll"
else:
    z3_library_file = "libz3.so"


solve_count = 0
cache_count = 0

from decimal import Decimal
import weakref

# import and set up Z3
import os
import z3

from ..errors import ClaripyZ3Error

_z3_paths = [ ]

if "Z3PATH" in os.environ:
    _z3_paths.append(os.environ["Z3PATH"])
if "VIRTUAL_ENV" in os.environ:
    virtual_env = os.environ["VIRTUAL_ENV"]
    _z3_paths.append(os.path.join(os.environ["VIRTUAL_ENV"], "lib"))
_z3_paths.extend(sys.path)
_z3_paths.append("/usr/lib")
_z3_paths.append("/usr/local/lib")
_z3_paths.append("/opt/python/lib")

for z3_path in _z3_paths:
    if not '.so' in z3_path and not '.dll' in z3_path:
        z3_path = os.path.join(z3_path, z3_library_file)
    if os.path.exists(z3_path):
        z3.init(z3_path)
        break
else:
    raise ClaripyZ3Error("Unable to find %s", z3_library_file)

supports_fp = hasattr(z3, 'fpEQ')

from ..backend import Backend

#pylint:disable=unidiomatic-typecheck

#import threading
#import functools
#z3_lock = threading.RLock()
#def synchronized(f):
#      @functools.wraps(f)
#      def synced(self, *args, **kwargs):
#          if not (self._background_solve or (self._background_solve is None and self._claripy.parallel)):
#              return f(self, *args, **kwargs)
#
#          try:
#              #while not z3_lock.acquire(blocking=False): print "ACQUIRING...",__import__('time').sleep(1)
#              z3_lock.acquire()
#              return f(self, *args, **kwargs)
#          finally:
#              z3_lock.release()
#      return synced

def condom(f):
    def z3_condom(*args, **kwargs):
        '''
        The Z3 condom intersects Z3Exceptions and throws a ClaripyZ3Error instead.
        '''
        try:
            args = tuple((int(a) if type(a) is long and a < sys.maxint else a) for a in args)
            return f(*args, **kwargs)
        except z3.Z3Exception as ze:
            raise ClaripyZ3Error("Z3Exception: %s" % ze)
    return z3_condom

class BackendZ3(Backend):
    _split_on = { 'And', 'Or' }

    def __init__(self):
        Backend.__init__(self, solver_required=True)
        self._enable_simplification_cache = False

        # and the operations
        all_ops = backend_fp_operations | backend_operations if supports_fp else backend_operations
        for o in all_ops - {'Reverse', 'fpToSBV', 'fpToUBV', 'SLT', 'SLE', 'SGT', 'SGE'}:
            self._op_raw[o] = getattr(z3, o)

        self._op_raw['SLT'] = self.SLT
        self._op_raw['SLE'] = self.SLE
        self._op_raw['SGT'] = self.SGT
        self._op_raw['SGE'] = self.SGE
        self._op_raw['Reverse'] = self.reverse
        self._op_raw['Identical'] = self.identical
        self._op_raw['I'] = lambda thing: thing
        self._op_raw['fpToSBV'] = self.fpToSBV
        self._op_raw['fpToUBV'] = self.fpToUBV

    @property
    def _ast_cache(self):
        try:
            return self._tls.ast_cache
        except AttributeError:
            self._tls.ast_cache = weakref.WeakValueDictionary()
            return self._tls.ast_cache

    @property
    def _var_cache(self):
        try:
            return self._tls.var_cache
        except AttributeError:
            self._tls.var_cache = weakref.WeakValueDictionary()
            return self._tls.var_cache

    @property
    def _sym_cache(self):
        try:
            return self._tls.sym_cache
        except AttributeError:
            self._tls.sym_cache = weakref.WeakValueDictionary()
            return self._tls.sym_cache

    @property
    def _simplification_cache_key(self):
        try:
            return self._tls.simplification_cache_key
        except AttributeError:
            self._tls.simplification_cache_key = weakref.WeakValueDictionary()
            return self._tls.simplification_cache_key

    @property
    def _simplification_cache_val(self):
        try:
            return self._tls.simplification_cache_val
        except AttributeError:
            self._tls.simplification_cache_val = weakref.WeakValueDictionary()
            return self._tls.simplification_cache_val

    def downsize(self):
        Backend.downsize(self)

        self._ast_cache.clear()
        self._var_cache.clear()
        self._sym_cache.clear()
        self._simplification_cache_key.clear()
        self._simplification_cache_val.clear()

    @condom
    def _size(self, e, result=None):
        if not isinstance(e, z3.BitVecRef) and not isinstance(e, z3.BitVecNumRef):
            l.debug("Unable to determine length of value of type %s", e.__class__)
            raise BackendError("Unable to determine length of value of type %s" % e.__class__)
        return e.size()

    def _name(self, e, result=None): #pylint:disable=unused-argument
        l.warning("BackendZ3.name() called. This is weird.")
        raise BackendError("name is not implemented yet")

    @staticmethod
    @condom
    def reverse(a):
        if a.size() == 8:
            return a
        elif a.size() % 8 != 0:
            raise ClaripyOperationError("can't reverse non-byte sized bitvectors")
        else:
            return z3.Concat(*[z3.Extract(i+7, i, a) for i in range(0, a.size(), 8)])

    @staticmethod
    @condom
    def SLT(a, b):
        return a < b

    @staticmethod
    @condom
    def SLE(a, b):
        return a <= b

    @staticmethod
    @condom
    def SGT(a, b):
        return a > b

    @staticmethod
    @condom
    def SGE(a, b):
        return a >= b

    @staticmethod
    @condom
    def fpToSBV(rm, fp, bv_len):
        return z3.fpToSBV(rm, fp, z3.BitVecSort(bv_len))

    @staticmethod
    @condom
    def fpToUBV(rm, fp, bv_len):
        return z3.fpToUBV(rm, fp, z3.BitVecSort(bv_len))

    def _identical(self, a, b, result=None):
        return a.eq(b)

    @condom
    def _convert(self, obj, result=None):
        if type(obj) is NativeBVV:
            return z3.BitVecVal(obj.value, obj.bits)
        elif isinstance(obj, FSort):
            return z3.FPSort(obj.exp, obj.mantissa)
        elif isinstance(obj, RM):
            if obj == RM_RNE:
                return z3.RNE()
            elif obj == RM_RNA:
                return z3.RNA()
            elif obj == RM_RTP:
                return z3.RTP()
            elif obj == RM_RTN:
                return z3.RTN()
            elif obj == RM_RTZ:
                return z3.RTZ()
            else:
                raise BackendError("unrecognized rounding mode")
        elif isinstance(obj, NativeFPV):
            val = str(obj.value)
            sort = self._convert(obj.sort)
            if val == 'inf':
                return z3.fpPlusInfinity(sort)
            elif val == '-inf':
                return z3.fpMinusInfinity(sort)
            elif val == '0.0':
                return z3.fpPlusZero(sort)
            elif val == '-0.0':
                return z3.fpMinusZero(sort)
            elif val == 'nan':
                return z3.fpNaN(sort)
            else:
                better_val = str(Decimal(obj.value))
                return z3.FPVal(better_val, sort)
        elif obj is True:
            return z3.BoolVal(True)
        elif obj is False:
            return z3.BoolVal(False)
        elif type(obj) in (int, long, float, str):
            return obj
        elif hasattr(obj, '__module__') and obj.__module__ == 'z3':
            return obj
        else:
            l.debug("BackendZ3 encountered unexpected type %s", type(obj))
            raise BackendError("unexpected type %s encountered in BackendZ3" % type(obj))

    @condom
    def call(self, *args, **kwargs):
        return Backend.call(self, *args, **kwargs)

    @condom
    def _abstract(self, z):
        #return self._abstract(z, split_on=split_on)[0]
        return self._abstract_internal(z.ctx.ctx, z.ast)

    @staticmethod
    def _z3_ast_hash(ctx, ast):
        """
        This is a better hashing function for z3 Ast objects. Z3_get_ast_hash() creates too many hash collisions.

        :param ctx: z3 Context
        :param ast: z3 Ast object
        :return: An integer - the hash
        """

        z3_hash = z3.Z3_get_ast_hash(ctx, ast)
        z3_ast_ref = ast.value # this seems to be the memory address
        z3_sort = z3.Z3_get_sort(ctx, ast).value
        return hash("%d_%d_%d" % (z3_hash, z3_sort, z3_ast_ref))

    def _abstract_internal(self, ctx, ast, split_on=None):
        h = self._z3_ast_hash(ctx, ast)
        try:
            return self._ast_cache[h]
        except KeyError:
            pass

        decl = z3.Z3_get_app_decl(ctx, ast)
        decl_num = z3.Z3_get_decl_kind(ctx, decl)
        z3_sort = z3.Z3_get_sort(ctx, ast)

        if decl_num not in z3_op_nums:
            raise ClaripyError("unknown decl kind %d" % decl_num)
        if z3_op_nums[decl_num] not in op_map:
            raise ClaripyError("unknown decl op %s" % z3_op_nums[decl_num])
        op_name = op_map[z3_op_nums[decl_num]]

        num_args = z3.Z3_get_app_num_args(ctx, ast)
        split_on = self._split_on if split_on is None else split_on
        new_split_on = split_on if op_name in split_on else set()
        children = [ self._abstract_internal(ctx, z3.Z3_get_app_arg(ctx, ast, i), new_split_on) for i in range(num_args) ]

        append_children = True

        if op_name == 'True':
            return BoolI(True)
        elif op_name == 'False':
            return BoolI(False)
        elif op_name.startswith('RM_'):
            return RM.from_name(op_name)
        elif op_name == 'BitVecVal':
            bv_num = long(z3.Z3_get_numeral_string(ctx, ast))
            bv_size = z3.Z3_get_bv_sort_size(ctx, z3_sort)
            return BVI(NativeBVV(bv_num, bv_size), length=bv_size)
        elif op_name == 'FPVal':
            # this is really imprecise
            fp_mantissa = float(z3.Z3_fpa_get_numeral_significand_string(ctx, ast))
            fp_exp = long(z3.Z3_fpa_get_numeral_exponent_string(ctx, ast))
            value = fp_mantissa * (2 ** fp_exp)

            ebits = z3.Z3_fpa_get_ebits(ctx, z3_sort)
            sbits = z3.Z3_fpa_get_sbits(ctx, z3_sort)
            sort = FSort.from_params(ebits, sbits)

            return FPI(NativeFPV(value, sort))
        elif op_name in ('MinusZero', 'MinusInf', 'PlusZero', 'PlusInf', 'NaN'):
            ebits = z3.Z3_fpa_get_ebits(ctx, z3_sort)
            sbits = z3.Z3_fpa_get_sbits(ctx, z3_sort)
            sort = FSort.from_params(ebits, sbits)

            if op_name == 'MinusZero':
                return FPI(NativeFPV(-0.0, sort))
            elif op_name == 'MinusInf':
                return FPI(NativeFPV(float('-inf'), sort))
            elif op_name == 'PlusZero':
                return FPI(NativeFPV(0.0, sort))
            elif op_name == 'PlusInf':
                return FPI(NativeFPV(float('inf'), sort))
            elif op_name == 'NaN':
                return FPI(NativeFPV(float('nan'), sort))
        elif op_name == 'UNINTERPRETED' and num_args == 0: # this *might* be a BitVec ;-)
            bv_name = z3.Z3_get_symbol_string(ctx, z3.Z3_get_decl_name(ctx, decl))
            bv_size = z3.Z3_get_bv_sort_size(ctx, z3_sort)

            #if bv_name.count('_') < 2:
            #      import ipdb; ipdb.set_trace()
            return BV("BitVec", (bv_name, bv_size), length=bv_size, variables={ bv_name }, symbolic=True)
        elif op_name == 'UNINTERPRETED':
            mystery_name = z3.Z3_get_symbol_string(ctx, z3.Z3_get_decl_name(ctx, decl))
            args = [ ]
            if mystery_name == 'bvsmod_i':
                op_name = '__mod__'
                decl_num = z3.Z3_OP_BSMOD
            elif mystery_name == 'bvsdiv_i':
                op_name = '__div__'
                decl_num = z3.Z3_OP_BSDIV
            else:
                l.error("Mystery operation %s in BackendZ3._abstract_internal. Please report this.", mystery_name)
        elif op_name == 'Extract':
            hi = z3.Z3_get_decl_int_parameter(ctx, decl, 0)
            lo = z3.Z3_get_decl_int_parameter(ctx, decl, 1)
            args = [ hi, lo ]
        elif op_name in ('SignExt', 'ZeroExt'):
            num = z3.Z3_get_decl_int_parameter(ctx, decl, 0)
            args = [ num ]
        elif op_name in ('fpToFP', 'fpToFPSigned'):
            exp = z3.Z3_fpa_get_ebits(ctx, z3_sort)
            mantissa = z3.Z3_fpa_get_sbits(ctx, z3_sort)
            sort = FSort.from_params(exp, mantissa)
            args = children + [sort]
            append_children = False
        elif op_name in ('fpToSBV', 'fpToUBV'):
            # uuuuuugggggghhhhhh
            bv_size = z3.Z3_get_bv_sort_size(ctx, z3_sort)
            args = children + [bv_size]
            append_children = False
        else:
            args = [ ]

        if append_children:
            args.extend(children)

        # fix up many-arg __add__
        if op_name in bin_ops and len(args) > 2:
            many_args = args #pylint:disable=unused-variable
            last = args[-1]
            rest = args[:-1]

            a = args[0].make_like(op_name, rest[:2])
            for b in rest[2:]:
                a = args[0].make_like(op_name, [a,b])
            args = [ a, last ]

        # hmm.... honestly not sure what to do here
        result_ty = op_type_map[z3_op_nums[decl_num]]
        ty = type(args[-1])

        if op_name == 'If':
            # If is polymorphic and thus must be handled specially
            ty = type(args[1])

            a = ty('If', tuple(args), length=args[1].length)
        else:
            if hasattr(ty, op_name) or hasattr(_all_operations, op_name):
                op = getattr(ty if hasattr(ty, op_name) else _all_operations, op_name)
                if op.calc_length is not None:
                    length = op.calc_length(*args)
                    a = result_ty(op_name, tuple(args), length=length)
                else:
                    a = result_ty(op_name, tuple(args))
            else:
                a = result_ty(op_name, tuple(args))

        self._ast_cache[h] = a
        return a

    def solver(self, timeout=None):
        s = z3.Solver()
        if timeout is not None:
            if 'soft_timeout' in str(s.param_descrs()):
                s.set('soft_timeout', timeout)
                s.set('solver2_timeout', timeout)
            else:
                s.set('timeout', timeout)
        return s

    def _add(self, s, c):
        s.add(*c)

    @condom
    def _check(self, s, extra_constraints=()):
        return self._check_and_model(s, extra_constraints=extra_constraints)[0]

    @condom
    def _check_and_model(self, s, extra_constraints=()): #pylint:disable=no-self-use
        global solve_count
        solve_count += 1
        if len(extra_constraints) > 0:
            s.push()
            s.add(*extra_constraints)

        l.debug("Doing a check!")
        #print "CHECKING"
        satness = s.check() == z3.sat
        if satness:
            model = s.model()
        else:
            model = None
        #print "CHECKED"

        if len(extra_constraints) > 0:
            s.pop()
        return satness, model

    @condom
    def _results(self, s, extra_constraints=(), generic_model=True):
        satness, z3_model = self._check_and_model(s, extra_constraints=extra_constraints)
        model = { }

        if satness:
            l.debug("sat!")
            if generic_model:
                for m_f in z3_model:
                    n = m_f.name()
                    m = m_f()
                    model[n] = model_object(z3_model.eval(m))
        else:
            l.debug("unsat!")

        return Result(satness, model, backend_model=z3_model)

    @condom
    def _eval(self, expr, n, extra_constraints=(), result=None, solver=None):
        global solve_count, cache_count

        #if n == 1 and model is None:
        #      import ipdb; ipdb.set_trace()

        results = [ ]
        model = result.backend_model if result else None
        if len(extra_constraints) > 0 or n != 1:
            solver.push()
        if len(extra_constraints) > 0:
            solver.add(*extra_constraints)
            model = None
            l.debug("Disregarding cache")

        for i in range(n):
            if model is None:
                solve_count += 1
                l.debug("Doing a check!")
                if solver.check() == z3.sat:
                    model = solver.model()
            else:
                cache_count += 1

            if model is None:
                break

            if not type(expr) in { int, float, str, bool, long }:
                v = model.eval(expr, model_completion=True)
            else:
                v = expr

            results.append(self._abstract(v))
            if i + 1 != n:
                solver.add(expr != v)
                model = None

        if len(extra_constraints) > 0 or n != 1:
            solver.pop()

        if len(results) == 0:
            raise UnsatError("constraints are unsat")

        return results

    @condom
    def _min(self, expr, extra_constraints=(), result=None, solver=None):
        global solve_count

        lo = 0
        hi = 2**expr.size()-1

        numpop = 0
        if len(extra_constraints) > 0:
            solver.push()
            numpop += 1
            solver.add(*[self.convert(e) for e in extra_constraints])

        while hi-lo > 1:
            middle = (lo + hi)/2
            #l.debug("h/m/l/d: %d %d %d %d", hi, middle, lo, hi-lo)

            solver.push()
            solver.add(z3.UGE(expr, lo), z3.ULE(expr, middle))
            numpop += 1

            solve_count += 1
            l.debug("Doing a check!")
            if solver.check() == z3.sat:
                l.debug("... still sat")
                hi = middle
            else:
                l.debug("... now unsat")
                lo = middle
                solver.pop()
                numpop -= 1

        for _ in range(numpop):
            solver.pop()

        #l.debug("final hi/lo: %d, %d", hi, lo)

        if hi == lo: return NativeBVV(lo, expr.size())
        else:
            solver.push()
            solver.add(expr == lo)
            l.debug("Doing a check!")
            if solver.check() == z3.sat:
                solver.pop()
                return NativeBVV(lo, expr.size())
            else:
                solver.pop()
        return NativeBVV(hi, expr.size())

    @condom
    def _max(self, expr, extra_constraints=(), result=None, solver=None):
        global solve_count

        lo = 0
        hi = 2**expr.size()-1

        numpop = 0
        if len(extra_constraints) > 0:
            solver.push()
            numpop += 1
            solver.add(*[self.convert(e) for e in extra_constraints])

        while hi-lo > 1:
            middle = (lo + hi)/2
            #l.debug("h/m/l/d: %d %d %d %d", hi, middle, lo, hi-lo)

            solver.push()
            solver.add(z3.UGT(expr, middle), z3.ULE(expr, hi))
            numpop += 1

            solve_count += 1
            l.debug("Doing a check!")
            if solver.check() == z3.sat:
                l.debug("... still sat")
                lo = middle
            else:
                l.debug("... now unsat")
                hi = middle
                solver.pop()
                numpop -= 1
            #l.debug("        now: %d %d %d %d", hi, middle, lo, hi-lo)

        for _ in range(numpop):
            solver.pop()

        if hi == lo: return NativeBVV(lo, expr.size())
        else:
            solver.push()
            solver.add(expr == hi)
            l.debug("Doing a check!")
            if solver.check() == z3.sat:
                solver.pop()
                return NativeBVV(hi, expr.size())
            else:
                solver.pop()
        return NativeBVV(lo, expr.size())

    def _simplify(self, expr): #pylint:disable=W0613,R0201
        raise Exception("This shouldn't be called. Bug Yan.")

    @condom
    def simplify(self, expr):
        if expr._simplified:
            return expr

        if self._enable_simplification_cache:
            try:
                k = self._simplification_cache_key[expr._cache_key]
                #print "HIT WEAK KEY CACHE"
                return k
            except KeyError:
                pass
            try:
                k = self._simplification_cache_val[expr._cache_key]
                #print "HIT WEAK VALUE CACHE"
                return k
            except KeyError:
                pass

            #print "MISS CACHE"

        l.debug("SIMPLIFYING EXPRESSION")

        #print "SIMPLIFYING"

        expr_raw = self.convert(expr)

        #l.debug("... before: %s (%s)", expr_raw, expr_raw.__class__.__name__)

        if isinstance(expr_raw, z3.BoolRef):
            tactics = z3.Then(z3.Tactic("simplify"), z3.Tactic("propagate-ineqs"), z3.Tactic("propagate-values"), z3.Tactic("unit-subsume-simplify"))
            s = tactics(expr_raw).as_expr()
            n = s.decl().name()

            if n == 'true':
                s = True
            elif n == 'false':
                s = False
        elif isinstance(expr_raw, z3.BitVecRef):
            s = z3.simplify(expr_raw)
        else:
            s = expr_raw

        for b in _eager_backends:
            try:
                o = self.wrap(b.convert(s))
                break
            except BackendError:
                continue
        else:
            o = self._abstract(s)

        #print "SIMPLIFIED"
        #l.debug("... after: %s (%s)", s, s.__class__.__name__)

        o._simplified = Base.FULL_SIMPLIFY

        if self._enable_simplification_cache:
            self._simplification_cache_val[expr._cache_key] = o
            self._simplification_cache_key[expr._cache_key] = o
        return o

    @staticmethod
    def wrap(e):
        if isinstance(e, (z3.BitVecRef, NativeBVV)):
            return BVI(e, length=e.size())
        elif isinstance(e, (z3.BoolRef, bool)):
            return BoolI(e)
        else:
            raise Exception("whoops")

    def _is_false(self, e):
        return z3.simplify(e).eq(z3.BoolVal(False))

    def _is_true(self, e):
        return z3.simplify(e).eq(z3.BoolVal(True))

    def _solution(self, expr, v, result=None, extra_constraints=(), solver=None):
        return self._check(solver, extra_constraints=(expr == v,) + tuple(extra_constraints))

#
# this is for the actual->abstract conversion above
#

# these are Z3 operation names for abstraction
z3_op_names = [ _ for _ in dir(z3) if _.startswith('Z3_OP') ]
z3_op_nums = { getattr(z3, _): _ for _ in z3_op_names }

#pylint:disable=bad-continuation
op_map = {
    # Boolean
    'Z3_OP_TRUE': 'True',
    'Z3_OP_FALSE': 'False',
    'Z3_OP_EQ': '__eq__',
    'Z3_OP_DISTINCT': '__ne__',
    'Z3_OP_ITE': 'If',
    'Z3_OP_AND': 'And',
    'Z3_OP_OR': 'Or',
    'Z3_OP_IFF': '__eq__',
    'Z3_OP_XOR': 'Xor',
    'Z3_OP_NOT': 'Not',
    'Z3_OP_IMPLIES': 'Implies',
    #'Z3_OP_OEQ': None,

    # Arithmetic
    #'Z3_OP_ANUM': None,
    #'Z3_OP_AGNUM': None,
    'Z3_OP_LE': 'SLE',
    'Z3_OP_GE': 'SGE',
    'Z3_OP_LT': 'SLT',
    'Z3_OP_GT': 'SGT',
    'Z3_OP_ADD': '__add__',
    'Z3_OP_SUB': '__sub__',
    'Z3_OP_UMINUS': '__neg__',
    'Z3_OP_MUL': '__mul__',
    'Z3_OP_DIV': '__div__',
    'Z3_OP_IDIV': '__div__',
    'Z3_OP_REM': '__mod__', # TODO: is this correct?
    'Z3_OP_MOD': '__mod__',
    #'Z3_OP_TO_REAL': None,
    #'Z3_OP_TO_INT': None,
    #'Z3_OP_IS_INT': None,
    'Z3_OP_POWER': '__pow__',

    # Arrays & Sets
    #'Z3_OP_STORE': None,
    #'Z3_OP_SELECT': None,
    #'Z3_OP_CONST_ARRAY': None,
    #'Z3_OP_ARRAY_MAP': None,
    #'Z3_OP_ARRAY_DEFAULT': None,
    #'Z3_OP_SET_UNION': None,
    #'Z3_OP_SET_INTERSECT': None,
    #'Z3_OP_SET_DIFFERENCE': None,
    #'Z3_OP_SET_COMPLEMENT': None,
    #'Z3_OP_SET_SUBSET': None,
    #'Z3_OP_AS_ARRAY': None,

    # Bit-vectors
    'Z3_OP_BNUM': 'BitVecVal',
    #'Z3_OP_BIT1': None, # MAYBE TODO
    #'Z3_OP_BIT0': None, # MAYBE TODO
    'Z3_OP_BNEG': '__neg__',
    'Z3_OP_BADD': '__add__',
    'Z3_OP_BSUB': '__sub__',
    'Z3_OP_BMUL': '__mul__',

    'Z3_OP_BSDIV': '__div__',
    'Z3_OP_BUDIV': '__div__', # TODO: is this correct?
    'Z3_OP_BSREM': '__mod__', # TODO: is this correct?
    'Z3_OP_BUREM': '__mod__', # TODO: is this correct?
    'Z3_OP_BSMOD': '__mod__', # TODO: is this correct?

    # special functions to record the division by 0 cases
    # these are internal functions
    #'Z3_OP_BSDIV0': None,
    #'Z3_OP_BUDIV0': None,
    #'Z3_OP_BSREM0': None,
    #'Z3_OP_BUREM0': None,
    #'Z3_OP_BSMOD0': None,

    'Z3_OP_ULEQ': 'ULE',
    'Z3_OP_SLEQ': 'SLE',
    'Z3_OP_UGEQ': 'UGE',
    'Z3_OP_SGEQ': 'SGE',
    'Z3_OP_ULT': 'ULT',
    'Z3_OP_SLT': 'SLT',
    'Z3_OP_UGT': 'UGT',
    'Z3_OP_SGT': 'SGT',

    'Z3_OP_BAND': '__and__',
    'Z3_OP_BOR': '__or__',
    'Z3_OP_BNOT': '__invert__',
    'Z3_OP_BXOR': '__xor__',
    #'Z3_OP_BNAND': None,
    #'Z3_OP_BNOR': None,
    #'Z3_OP_BXNOR': None,

    'Z3_OP_CONCAT': 'Concat',
    'Z3_OP_SIGN_EXT': 'SignExt',
    'Z3_OP_ZERO_EXT': 'ZeroExt',
    'Z3_OP_EXTRACT': 'Extract',
    'Z3_OP_REPEAT': 'RepeatBitVec',

    #'Z3_OP_BREDOR': None,
    #'Z3_OP_BREDAND': None,
    #'Z3_OP_BCOMP': None,

    'Z3_OP_BSHL': '__lshift__',
    'Z3_OP_BLSHR': 'LShR',
    'Z3_OP_BASHR': '__rshift__',
    #'Z3_OP_ROTATE_LEFT': None,
    #'Z3_OP_ROTATE_RIGHT': None,
    'Z3_OP_EXT_ROTATE_LEFT': 'RotateLeft',
    'Z3_OP_EXT_ROTATE_RIGHT': 'RotateRight',

    'Z3_OP_FPA_TO_SBV': 'fpToSBV',
    'Z3_OP_FPA_TO_UBV': 'fpToUBV',
    'Z3_OP_FPA_TO_IEEE_BV': 'fpToIEEEBV',
    'Z3_OP_FPA_TO_FP': 'fpToFP',
    'Z3_OP_FPA_NUM': 'FPVal',

    'Z3_OP_FPA_MINUS_ZERO': 'MinusZero',
    'Z3_OP_FPA_MINUS_INF': 'MinusInf',
    'Z3_OP_FPA_PLUS_ZERO': 'PlusZero',
    'Z3_OP_FPA_PLUS_INF': 'PlusInf',
    'Z3_OP_FPA_NAN': 'NaN',

    'Z3_OP_FPA_EQ': 'fpEQ',
    'Z3_OP_FPA_GT': 'fpGT',
    'Z3_OP_FPA_GE': 'fpGEQ',
    'Z3_OP_FPA_LT': 'fpLT',
    'Z3_OP_FPA_LE': 'fpLEQ',

    'Z3_OP_FPA_ABS': 'fpAbs',
    'Z3_OP_FPA_NEG': 'fpNeg',
    'Z3_OP_FPA_ADD': 'fpAdd',
    'Z3_OP_FPA_SUB': 'fpSub',
    'Z3_OP_FPA_MUL': 'fpMul',
    'Z3_OP_FPA_DIV': 'fpDiv',

    'Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN': 'RM_RNE',
    'Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY': 'RM_RNA',
    'Z3_OP_FPA_RM_TOWARD_ZERO': 'RM_RTZ',
    'Z3_OP_FPA_RM_TOWARD_POSITIVE': 'RM_RTP',
    'Z3_OP_FPA_RM_TOWARD_NEGATIVE': 'RM_RTN',

    'Z3_OP_UNINTERPRETED': 'UNINTERPRETED'
}

from ..ast.base import Base, model_object
from ..ast.bv import BV, BVI
from ..ast.bool import BoolI, Bool
from ..ast.fp import FP, FPI
from ..operations import backend_operations, backend_fp_operations, bin_ops
from ..result import Result
from ..bv import BVV as NativeBVV
from ..fp import FPV as NativeFPV, FSort, RM, RM_RNE, RM_RNA, RM_RTP, RM_RTN, RM_RTZ
from ..errors import ClaripyError, BackendError, UnsatError, ClaripyOperationError
from .. import _eager_backends, _all_operations

op_type_map = {
    # Boolean
    'Z3_OP_TRUE': Bool,
    'Z3_OP_FALSE': Bool,
    'Z3_OP_EQ': Bool,
    'Z3_OP_DISTINCT': Bool,
    'Z3_OP_ITE': Bool,
    'Z3_OP_AND': Bool,
    'Z3_OP_OR': Bool,
    'Z3_OP_IFF': Bool,
    'Z3_OP_XOR': Bool,
    'Z3_OP_NOT': Bool,
    'Z3_OP_IMPLIES': Bool,
    #'Z3_OP_OEQ': None,

    # Arithmetic
    #'Z3_OP_ANUM': None,
    #'Z3_OP_AGNUM': None,
    'Z3_OP_LE': None,
    'Z3_OP_GE': None,
    'Z3_OP_LT': None,
    'Z3_OP_GT': None,
    'Z3_OP_ADD': None,
    'Z3_OP_SUB': None,
    'Z3_OP_UMINUS': None,
    'Z3_OP_MUL': None,
    'Z3_OP_DIV': None,
    'Z3_OP_IDIV': None,
    'Z3_OP_REM': None, # TODO: is this correct?
    'Z3_OP_MOD': None,
    #'Z3_OP_TO_REAL': None,
    #'Z3_OP_TO_INT': None,
    #'Z3_OP_IS_INT': None,
    'Z3_OP_POWER': None,

    # Arrays & Sets
    #'Z3_OP_STORE': None,
    #'Z3_OP_SELECT': None,
    #'Z3_OP_CONST_ARRAY': None,
    #'Z3_OP_ARRAY_MAP': None,
    #'Z3_OP_ARRAY_DEFAULT': None,
    #'Z3_OP_SET_UNION': None,
    #'Z3_OP_SET_INTERSECT': None,
    #'Z3_OP_SET_DIFFERENCE': None,
    #'Z3_OP_SET_COMPLEMENT': None,
    #'Z3_OP_SET_SUBSET': None,
    #'Z3_OP_AS_ARRAY': None,

    # Bit-vectors
    'Z3_OP_BNUM': 'BitVecVal',
    #'Z3_OP_BIT1': None, # MAYBE TODO
    #'Z3_OP_BIT0': None, # MAYBE TODO
    'Z3_OP_BNEG': BV,
    'Z3_OP_BADD': BV,
    'Z3_OP_BSUB': BV,
    'Z3_OP_BMUL': BV,

    'Z3_OP_BSDIV': BV,
    'Z3_OP_BUDIV': BV,
    'Z3_OP_BSREM': BV,
    'Z3_OP_BUREM': BV,
    'Z3_OP_BSMOD': BV,

    # special functions to record the division by 0 cases
    # these are internal functions
    #'Z3_OP_BSDIV0': None,
    #'Z3_OP_BUDIV0': None,
    #'Z3_OP_BSREM0': None,
    #'Z3_OP_BUREM0': None,
    #'Z3_OP_BSMOD0': None,

    'Z3_OP_ULEQ': Bool,
    'Z3_OP_SLEQ': Bool,
    'Z3_OP_UGEQ': Bool,
    'Z3_OP_SGEQ': Bool,
    'Z3_OP_ULT': Bool,
    'Z3_OP_SLT': Bool,
    'Z3_OP_UGT': Bool,
    'Z3_OP_SGT': Bool,

    'Z3_OP_BAND': BV,
    'Z3_OP_BOR': BV,
    'Z3_OP_BNOT': BV,
    'Z3_OP_BXOR': BV,
    #'Z3_OP_BNAND': None,
    #'Z3_OP_BNOR': None,
    #'Z3_OP_BXNOR': None,

    'Z3_OP_CONCAT': BV,
    'Z3_OP_SIGN_EXT': BV,
    'Z3_OP_ZERO_EXT': BV,
    'Z3_OP_EXTRACT': BV,
    'Z3_OP_REPEAT': BV,

    #'Z3_OP_BREDOR': None,
    #'Z3_OP_BREDAND': None,
    #'Z3_OP_BCOMP': None,

    'Z3_OP_BSHL': BV,
    'Z3_OP_BLSHR': BV,
    'Z3_OP_BASHR': BV,
    #'Z3_OP_ROTATE_LEFT': None,
    #'Z3_OP_ROTATE_RIGHT': None,
    'Z3_OP_EXT_ROTATE_LEFT': BV,
    'Z3_OP_EXT_ROTATE_RIGHT': BV,

    'Z3_OP_FPA_TO_SBV': BV,
    'Z3_OP_FPA_TO_UBV': BV,
    'Z3_OP_FPA_TO_IEEE_BV': BV,
    'Z3_OP_FPA_TO_FP': FP,
    'Z3_OP_FPA_NUM': FP,

    'Z3_OP_FPA_MINUS_ZERO': FP,
    'Z3_OP_FPA_MINUS_INF': FP,
    'Z3_OP_FPA_PLUS_ZERO': FP,
    'Z3_OP_FPA_PLUS_INF': FP,
    'Z3_OP_FPA_NAN': FP,

    'Z3_OP_FPA_EQ': Bool,
    'Z3_OP_FPA_GT': Bool,
    'Z3_OP_FPA_GE': Bool,
    'Z3_OP_FPA_LT': Bool,
    'Z3_OP_FPA_LE': Bool,

    'Z3_OP_FPA_ABS': FP,
    'Z3_OP_FPA_NEG': FP,
    'Z3_OP_FPA_ADD': FP,
    'Z3_OP_FPA_SUB': FP,
    'Z3_OP_FPA_MUL': FP,
    'Z3_OP_FPA_DIV': FP,

    'Z3_OP_UNINTERPRETED': 'UNINTERPRETED'
}
