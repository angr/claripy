import sys
import ctypes
import logging
import weakref
import operator
import threading
from decimal import Decimal
l = logging.getLogger("claripy.backends.backend_z3")

#pylint:disable=unidiomatic-typecheck

#
# Some global variables
#

# track the count of solves
solve_count = 0

#
# Import and set up Z3
#

import os
import z3

if sys.platform == 'darwin':
    z3_library_file = "libz3.dylib"
elif sys.platform == 'win32':
    z3_library_file = "libz3.dll"
else:
    z3_library_file = "libz3.so"

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
_z3_paths.append(os.path.join(sys.prefix, "lib"))

try:
    z3.z3core.lib()
except:
    for z3_path in _z3_paths:
        if not '.so' in z3_path and \
                not '.dll' in z3_path and \
                not '.dylib' in z3_path:
            z3_path = os.path.join(z3_path, z3_library_file)
        if os.path.exists(z3_path):
            z3.init(z3_path)
            break
    else:
        raise ClaripyZ3Error("Unable to find %s", z3_library_file)

supports_fp = hasattr(z3, 'fpEQ')

#
# Utility functions
#

def condom(f):
    def z3_condom(*args, **kwargs):
        """
        The Z3 condom intercepts Z3Exceptions and throws a ClaripyZ3Error instead.
        """
        try:
            condom_args = tuple((int(a) if type(a) is long and a < sys.maxint else a) for a in args)
            return f(*condom_args, **kwargs)
        except z3.Z3Exception as ze:
            _, _, traceback = sys.exc_info()
            raise ClaripyZ3Error, ("Z3Exception: %s" % ze), traceback
    return z3_condom

def _raw_caller(f):
    @staticmethod
    @condom
    def raw_caller(*args, **kwargs):
        return f(*args, **kwargs)
    return raw_caller

#
# And the (ugh) magic
#

from . import Backend
class BackendZ3(Backend):
    _split_on = { 'And', 'Or' }

    def __init__(self):
        Backend.__init__(self, solver_required=True)
        self._enable_simplification_cache = False

        # and the operations
        all_ops = backend_fp_operations | backend_operations if supports_fp else backend_operations
        for o in all_ops - {'BVV', 'BoolV', 'FPV', 'FP', 'BitVec'}:
            self._op_raw[o] = getattr(self, '_op_raw_' + o)

        self._op_raw['__ge__'] = self._op_raw_UGE
        self._op_raw['__gt__'] = self._op_raw_UGT
        self._op_raw['__le__'] = self._op_raw_ULE
        self._op_raw['__lt__'] = self._op_raw_ULT

        self._op_raw['Reverse'] = self._op_raw_Reverse
        self._op_raw['Identical'] = self._identical
        self._op_raw['fpToSBV'] = self._op_raw_fpToSBV
        self._op_raw['fpToUBV'] = self._op_raw_fpToUBV

        self._op_expr['BVS'] = self.BVS
        self._op_expr['BVV'] = self.BVV
        self._op_expr['FPV'] = self.FPV
        self._op_expr['FPS'] = self.FPS
        self._op_expr['BoolV'] = self.BoolV
        self._op_expr['BoolS'] = self.BoolS

        self._op_raw['__div__'] = self._op_div
        self._op_raw['__mod__'] = self._op_mod

        # reduceable
        self._op_raw['__add__'] = self._op_add
        self._op_raw['__sub__'] = self._op_sub
        self._op_raw['__mul__'] = self._op_mul
        self._op_raw['__or__'] = self._op_or
        self._op_raw['__xor__'] = self._op_xor
        self._op_raw['__and__'] = self._op_and


    @property
    def _c_uint64_p(self):
        try:
            return self._tls.c_uint64_p
        except AttributeError:
            # a pointer to get values out of Z3
            self._tls.c_uint64_p = ctypes.pointer(ctypes.c_uint64())

            return self._tls.c_uint64_p

    @property
    def _context(self):
        try:
            return self._tls.context
        except AttributeError:
            self._tls.context = z3.Context() if threading.current_thread().name != 'MainThread' else z3.main_ctx()
            return self._tls.context

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
    def _size(self, e):
        if not isinstance(e, z3.BitVecRef) and not isinstance(e, z3.BitVecNumRef):
            l.debug("Unable to determine length of value of type %s", e.__class__)
            raise BackendError("Unable to determine length of value of type %s" % e.__class__)
        return e.size()

    def _name(self, e): #pylint:disable=unused-argument
        l.warning("BackendZ3.name() called. This is weird.")
        raise BackendError("name is not implemented yet")

    #
    # Core creation methods
    #

    @condom
    def BVS(self, ast): #pylint:disable=unused-argument
        name, mn, mx, stride, _, _, _ = ast.args #pylint:disable=unused-variable
        size = ast.size()
        expr = z3.BitVec(name, size, ctx=self._context)
        #if mn is not None:
        #    expr = z3.If(z3.ULT(expr, mn), mn, expr, ctx=self._context)
        #if mx is not None:
        #    expr = z3.If(z3.UGT(expr, mx), mx, expr, ctx=self._context)
        #if stride is not None:
        #    expr = (expr / stride) * stride
        return expr

    @condom
    def BVV(self, ast): #pylint:disable=unused-argument
        if ast.args[0] is None:
            raise BackendError("Z3 can't handle empty BVVs")

        size = ast.size()
        return z3.BitVecVal(ast.args[0], size, ctx=self._context)

    @staticmethod
    @condom
    def FPS(name, sort): #pylint:disable=unused-argument
        raise BackendError("TODO: not sure how to do this")

    @condom
    def FPV(self, ast): #pylint:disable=unused-argument
        val = str(ast.args[0])
        sort = self._convert(ast.args[1])
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
            better_val = str(Decimal(ast.args[0]))
            return z3.FPVal(better_val, sort, ctx=self._context)

    @condom
    def BoolS(self, ast): #pylint:disable=unused-argument
        return z3.Bool(ast.args[0], ctx=self._context)

    @condom
    def BoolV(self, ast): #pylint:disable=unused-argument
        return z3.BoolVal(ast.args[0], ctx=self._context)

    #
    # Conversions
    #

    @condom
    def _convert(self, obj):
        if isinstance(obj, FSort):
            return z3.FPSort(obj.exp, obj.mantissa, ctx=self._context)
        elif isinstance(obj, RM):
            if obj == RM_RNE:
                return z3.RNE(ctx=self._context)
            elif obj == RM_RNA:
                return z3.RNA(ctx=self._context)
            elif obj == RM_RTP:
                return z3.RTP(ctx=self._context)
            elif obj == RM_RTN:
                return z3.RTN(ctx=self._context)
            elif obj == RM_RTZ:
                return z3.RTZ(ctx=self._context)
            else:
                raise BackendError("unrecognized rounding mode")
        elif obj is True:
            return z3.BoolVal(True, ctx=self._context)
        elif obj is False:
            return z3.BoolVal(False, ctx=self._context)
        elif type(obj) in (int, long, float, str):
            return obj
        elif hasattr(obj, '__module__') and obj.__module__ in ('z3', 'z3.z3'):
            return obj
        else:
            l.debug("BackendZ3 encountered unexpected type %s", type(obj))
            raise BackendError("unexpected type %s encountered in BackendZ3" % type(obj))

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

        :param ctx: A z3 Context.
        :param ast: A z3 Ast object.
        :return:    An integer - the hash.
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
            return BoolV(True)
        elif op_name == 'False':
            return BoolV(False)
        elif op_name.startswith('RM_'):
            return RM.from_name(op_name)
        elif op_name == 'BitVecVal':
            bv_size = z3.Z3_get_bv_sort_size(ctx, z3_sort)
            if z3.Z3_get_numeral_uint64(ctx, ast, self._c_uint64_p):
                return BVV(self._c_uint64_p.contents.value, bv_size)
            else:
                bv_num = long(z3.Z3_get_numeral_string(ctx, ast))
                return BVV(bv_num, bv_size)
        elif op_name == 'FPVal':
            # this is really imprecise
            fp_mantissa = float(z3.Z3_fpa_get_numeral_significand_string(ctx, ast))
            fp_exp = long(z3.Z3_fpa_get_numeral_exponent_string(ctx, ast))
            value = fp_mantissa * (2 ** fp_exp)

            ebits = z3.Z3_fpa_get_ebits(ctx, z3_sort)
            sbits = z3.Z3_fpa_get_sbits(ctx, z3_sort)
            sort = FSort.from_params(ebits, sbits)

            return FPV(value, sort)
        elif op_name in ('MinusZero', 'MinusInf', 'PlusZero', 'PlusInf', 'NaN'):
            ebits = z3.Z3_fpa_get_ebits(ctx, z3_sort)
            sbits = z3.Z3_fpa_get_sbits(ctx, z3_sort)
            sort = FSort.from_params(ebits, sbits)

            if op_name == 'MinusZero':
                return FPV(-0.0, sort)
            elif op_name == 'MinusInf':
                return FPV(float('-inf'), sort)
            elif op_name == 'PlusZero':
                return FPV(0.0, sort)
            elif op_name == 'PlusInf':
                return FPV(float('inf'), sort)
            elif op_name == 'NaN':
                return FPV(float('nan'), sort)
        elif op_name == 'UNINTERPRETED' and num_args == 0: # this *might* be a BitVec ;-)
            bv_name = z3.Z3_get_symbol_string(ctx, z3.Z3_get_decl_name(ctx, decl))
            bv_size = z3.Z3_get_bv_sort_size(ctx, z3_sort)

            #if bv_name.count('_') < 2:
            #       import ipdb; ipdb.set_trace()
            return BV("BVS", (bv_name, None, None, None, False, False, None), length=bv_size, variables={ bv_name }, symbolic=True)
        elif op_name == 'UNINTERPRETED':
            mystery_name = z3.Z3_get_symbol_string(ctx, z3.Z3_get_decl_name(ctx, decl))
            args = [ ]

            #
            # TODO: DEPRECATED: remove the following after some reasonable amount of time.
            #

            if mystery_name == 'bvsmod_i':
                l.error("Your Z3 is out of date. Please update angr-only-z3-custom or future releases of claripy will fail.")
                op_name = '__mod__'
                decl_num = z3.Z3_OP_BSMOD
            elif mystery_name == 'bvsdiv_i':
                l.error("Your Z3 is out of date. Please update angr-only-z3-custom or future releases of claripy will fail.")
                op_name = 'SDiv'
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

        # hmm.... honestly not sure what to do here
        result_ty = op_type_map[z3_op_nums[decl_num]]
        ty = type(args[-1])

        if type(result_ty) is str:
            err = "Unknown Z3 error in abstraction (result_ty == '%s'). Update your version of Z3, and, if the problem persists, open a claripy issue." % result_ty
            l.error(err)
            raise BackendError(err)

        if op_name == 'If':
            # If is polymorphic and thus must be handled specially
            ty = type(args[1])

            a = ty('If', tuple(args), length=args[1].length)
        elif hasattr(ty, op_name) or hasattr(_all_operations, op_name):
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

    def _abstract_to_primitive(self, ctx, ast):
        decl = z3.Z3_get_app_decl(ctx, ast)
        decl_num = z3.Z3_get_decl_kind(ctx, decl)

        if decl_num not in z3_op_nums:
            raise ClaripyError("unknown decl kind %d" % decl_num)
        if z3_op_nums[decl_num] not in op_map:
            raise ClaripyError("unknown decl op %s" % z3_op_nums[decl_num])
        op_name = op_map[z3_op_nums[decl_num]]

        if op_name == 'BitVecVal':
            if z3.Z3_get_numeral_uint64(ctx, ast, self._c_uint64_p):
                return self._c_uint64_p.contents.value
            else:
                bv_num = long(z3.Z3_get_numeral_string(ctx, ast))
                return bv_num
        elif op_name == 'FPVal':
            # this is really imprecise
            fp_mantissa = float(z3.Z3_fpa_get_numeral_significand_string(ctx, ast))
            fp_exp = long(z3.Z3_fpa_get_numeral_exponent_string(ctx, ast))
            return fp_mantissa * (2 ** fp_exp)
        elif op_name == 'True':
            return True
        elif op_name == 'False':
            return False
        else:
            raise BackendError("Unable to abstract Z3 object to primitive")

    def solver(self, timeout=None):
        s = z3.Solver(ctx=self._context)
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
    def _primitive_from_model(self, model, expr):
        v = model.eval(expr, model_completion=True)
        return self._abstract_to_primitive(v.ctx.ctx, v.ast)

    #
    # New, model-driven solves
    #

    def _generic_model(self, z3_model):
        """
        Converts a Z3 model to a name->primitive dict.
        """
        model = { }
        for m_f in z3_model:
            n = m_f.name()
            m = m_f()
            me = z3_model.eval(m)
            model[n] = self._abstract_to_primitive(me.ctx.ctx, me.ast)

        return model

    def _satisfiable(self, extra_constraints=(), solver=None, model_callback=None):
        global solve_count

        solve_count += 1
        if len(extra_constraints) > 0:
            solver.push()
            solver.add(*extra_constraints)

        try:

            l.debug("Doing a check!")
            #print "CHECKING"
            if solver.check() != z3.sat:
                return False

            if model_callback is not None:
                model_callback(self._generic_model(solver.model()))
        finally:
            if len(extra_constraints) > 0:
                solver.pop()
        return True

    def _eval(self, expr, n, extra_constraints=(), solver=None, model_callback=None):
        results = self._batch_eval(
            [ expr ], n, extra_constraints=extra_constraints,
            solver=solver, model_callback=model_callback
        )

        # Unpack it
        return [ v[0] for v in results ]

    @condom
    def _batch_eval(self, exprs, n, extra_constraints=(), solver=None, model_callback=None):
        global solve_count

        result_values = [ ]

        if len(extra_constraints) > 0 or n != 1:
            solver.push()
        if len(extra_constraints) > 0:
            solver.add(*extra_constraints)

        for i in range(n):
            solve_count += 1
            l.debug("Doing a check!")
            if solver.check() != z3.sat:
                break
            model = solver.model()

            # construct results
            r = [ ]
            for expr in exprs:
                if not type(expr) in {int, float, str, bool, long}:
                    v = self._primitive_from_model(model, expr)
                    r.append(v)
                else:
                    r.append(expr)

            # Append the solution to the result list
            if model_callback is not None:
                model_callback(self._generic_model(solver.model()))
            result_values.append(tuple(r))

            # Construct the extra constraint so we don't get the same result anymore
            if i + 1 != n:
                solver.add(self._op_raw_Not(self._op_raw_And(*[(ex == ex_v) for ex, ex_v in zip(exprs, r)])))
                model = None

        if len(extra_constraints) > 0 or n != 1:
            solver.pop()

        return result_values

    @condom
    def _min(self, expr, extra_constraints=(), solver=None, model_callback=None):
        global solve_count

        lo = 0
        hi = 2**expr.size()-1
        vals = set()

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
                if model_callback is not None:
                    model_callback(self._generic_model(solver.model()))
                vals.add(self._primitive_from_model(solver.model(), expr))
                hi = middle
            else:
                l.debug("... now unsat")
                lo = middle
                solver.pop()
                numpop -= 1

        for _ in range(numpop):
            solver.pop()

        #l.debug("final hi/lo: %d, %d", hi, lo)

        if hi == lo: return lo
        else:
            solver.push()
            solver.add(expr == lo)
            l.debug("Doing a check!")
            if solver.check() == z3.sat:
                if model_callback is not None:
                    model_callback(self._generic_model(solver.model()))
                vals.add(lo)
                solver.pop()
            else:
                vals.add(hi)
                solver.pop()

        return min(vals)

    @condom
    def _max(self, expr, extra_constraints=(), solver=None, model_callback=None):
        global solve_count

        lo = 0
        hi = 2**expr.size()-1
        vals = set()

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
                vals.add(self._primitive_from_model(solver.model(), expr))
                if model_callback is not None:
                    model_callback(self._generic_model(solver.model()))
            else:
                l.debug("... now unsat")
                hi = middle
                solver.pop()
                numpop -= 1
            #l.debug("          now: %d %d %d %d", hi, middle, lo, hi-lo)

        for _ in range(numpop):
            solver.pop()

        if hi == lo:
            vals.add(hi)
        else:
            solver.push()
            solver.add(expr == hi)
            l.debug("Doing a check!")
            if solver.check() == z3.sat:
                if model_callback is not None:
                    model_callback(self._generic_model(solver.model()))
                vals.add(hi)
                solver.pop()
            else:
                vals.add(lo)
                solver.pop()

        return max(vals)

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

        #s = expr_raw
        if isinstance(expr_raw, z3.BoolRef):
            tactics = z3.Then(
                z3.Tactic("simplify", ctx=self._context),
                z3.Tactic("propagate-ineqs", ctx=self._context),
                z3.Tactic("propagate-values", ctx=self._context),
                z3.Tactic("unit-subsume-simplify", ctx=self._context),
                ctx=self._context
            )
            s = tactics(expr_raw).as_expr()
            #n = s.decl().name()
            #if n == 'true':
            #    s = True
            #elif n == 'false':
            #    s = False
        elif isinstance(expr_raw, z3.BitVecRef):
            s = z3.simplify(expr_raw)
        else:
            s = expr_raw

        o = self._abstract(s)
        o._simplified = Base.FULL_SIMPLIFY

        if self._enable_simplification_cache:
            self._simplification_cache_val[expr._cache_key] = o
            self._simplification_cache_key[expr._cache_key] = o
        return o

    def _is_false(self, e, extra_constraints=(), solver=None, model_callback=None):
        return z3.simplify(e).eq(z3.BoolVal(False, ctx=self._context))

    def _is_true(self, e, extra_constraints=(), solver=None, model_callback=None):
        return z3.simplify(e).eq(z3.BoolVal(True, ctx=self._context))

    def _solution(self, expr, v, extra_constraints=(), solver=None, model_callback=None):
        return self._satisfiable(extra_constraints=(expr == v,) + tuple(extra_constraints), solver=solver, model_callback=model_callback)

    #
    # Some Z3 passthroughs
    #

    # these require the context or special treatment

    @staticmethod
    def _op_div(a, b):
        return z3.UDiv(a, b)
    @staticmethod
    def _op_mod(a, b):
        return z3.URem(a, b)
    @staticmethod
    def _op_add(*args):
        return reduce(operator.__add__, args)
    @staticmethod
    def _op_sub(*args):
        return reduce(operator.__sub__, args)
    @staticmethod
    def _op_mul(*args):
        return reduce(operator.__mul__, args)
    @staticmethod
    def _op_or(*args):
        return reduce(operator.__or__, args)
    @staticmethod
    def _op_xor(*args):
        return reduce(operator.__xor__, args)
    @staticmethod
    def _op_and(*args):
        return reduce(operator.__and__, args)

    def _op_raw_And(self, *args):
        return z3.And(*(tuple(args) + ( self._context, )))

    def _op_raw_Or(self, *args):
        return z3.Or(*(tuple(args) + ( self._context, )))

    def _op_raw_Not(self, a):
        return z3.Not(a, ctx=self._context)

    def _op_raw_If(self, i, t, e):
        return z3.If(i, t, e, ctx=self._context)

    @condom
    def _op_raw_fpAbs(self, a):
        return z3.fpAbs(a, ctx=self._context)

    @condom
    def _op_raw_fpNeg(self, a):
        return z3.fpNeg(a, ctx=self._context)

    @condom
    def _op_raw_fpAdd(self, rm, a, b):
        return z3.fpAdd(rm, a, b, ctx=self._context)

    @condom
    def _op_raw_fpSub(self, rm, a, b):
        return z3.fpSub(rm, a, b, ctx=self._context)

    @condom
    def _op_raw_fpMul(self, rm, a, b):
        return z3.fpMul(rm, a, b, ctx=self._context)

    @condom
    def _op_raw_fpDiv(self, rm, a, b):
        return z3.fpDiv(rm, a, b, ctx=self._context)

    @condom
    def _op_raw_fpLT(self, a, b):
        return z3.fpLT(a, b, ctx=self._context)

    @condom
    def _op_raw_fpLEQ(self, a, b):
        return z3.fpLEQ(a, b, ctx=self._context)

    @condom
    def _op_raw_fpGT(self, a, b):
        return z3.fpGT(a, b, ctx=self._context)

    @condom
    def _op_raw_fpGEQ(self, a, b):
        return z3.fpGEQ(a, b, ctx=self._context)

    @condom
    def _op_raw_fpEQ(self, a, b):
        return z3.fpEQ(a, b, ctx=self._context)

    @condom
    def _op_raw_fpFP(self, sgn, exp, sig):
        return z3.fpFP(sgn, exp, sig, ctx=self._context)

    @condom
    def _op_raw_fpToSBV(self, rm, fp, bv_len):
        return z3.fpToSBV(rm, fp, z3.BitVecSort(bv_len, ctx=self._context))

    @condom
    def _op_raw_fpToUBV(self, rm, fp, bv_len):
        return z3.fpToUBV(rm, fp, z3.BitVecSort(bv_len, ctx=self._context))

    @condom
    def _op_raw_fpToFP(self, a1, a2=None, a3=None):
        return z3.fpToFP(a1, a2=a2, a3=a3, ctx=self._context)

    @condom
    def _op_raw_fpToIEEEBV(self, x):
        return z3.fpToIEEEBV(x, ctx=self._context)

    # and these do not
    _op_raw_Concat = _raw_caller(z3.Concat)
    _op_raw_Extract = _raw_caller(z3.Extract)
    _op_raw_LShR = _raw_caller(z3.LShR)
    _op_raw_RotateLeft = _raw_caller(z3.RotateLeft)
    _op_raw_RotateRight = _raw_caller(z3.RotateRight)
    _op_raw_SignExt = _raw_caller(z3.SignExt)
    _op_raw_UGE = _raw_caller(z3.UGE)
    _op_raw_UGT = _raw_caller(z3.UGT)
    _op_raw_ULE = _raw_caller(z3.ULE)
    _op_raw_ULT = _raw_caller(z3.ULT)
    _op_raw_ZeroExt = _raw_caller(z3.ZeroExt)
    _op_raw_SMod = _raw_caller(z3.SRem)

    @staticmethod
    @condom
    def _op_raw_Reverse(a):
        if a.size() == 8:
            return a
        elif a.size() % 8 != 0:
            raise ClaripyOperationError("can't reverse non-byte sized bitvectors")
        else:
            return z3.Concat(*[z3.Extract(i+7, i, a) for i in range(0, a.size(), 8)])

    @staticmethod
    @condom
    def _op_raw_SLT(a, b):
        return a < b

    @staticmethod
    @condom
    def _op_raw_SLE(a, b):
        return a <= b

    @staticmethod
    @condom
    def _op_raw_SGT(a, b):
        return a > b

    @staticmethod
    @condom
    def _op_raw_SGE(a, b):
        return a >= b

    @staticmethod
    @condom
    def _op_raw_SDiv(a, b):
        return a / b

    def _identical(self, a, b):
        return a.eq(b)

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
    'Z3_OP_DIV': 'SDiv',
    'Z3_OP_IDIV': 'SDiv',
    'Z3_OP_REM': '__mod__',
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

    'Z3_OP_BSDIV': 'SDiv',
    'Z3_OP_BUDIV': '__div__',
    'Z3_OP_BSREM': 'SMod',
    'Z3_OP_BUREM': '__mod__',
    'Z3_OP_BSMOD': 'SMod',
    'Z3_OP_BSDIV_I': 'SDiv',
    'Z3_OP_BUDIV_I': '__div__',
    'Z3_OP_BSREM_I': 'SMod',
    'Z3_OP_BUREM_I': '__mod__',
    'Z3_OP_BSMOD_I': 'SMod',

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

from ..ast.base import Base
from ..ast.bv import BV, BVV
from ..ast.bool import BoolV, Bool
from ..ast.fp import FP, FPV
from ..operations import backend_operations, backend_fp_operations
from ..fp import FSort, RM, RM_RNE, RM_RNA, RM_RTP, RM_RTN, RM_RTZ
from ..errors import ClaripyError, BackendError, ClaripyOperationError
from .. import _all_operations

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
    'Z3_OP_BSDIV_I': BV,
    'Z3_OP_BUDIV_I': BV,
    'Z3_OP_BSREM_I': BV,
    'Z3_OP_BUREM_I': BV,
    'Z3_OP_BSMOD_I': BV,

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
