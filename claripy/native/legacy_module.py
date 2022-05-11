from .clari_setup import clari

from collections import defaultdict
from enum import Enum
import re


def _gen_ctor_type_map():
    Create = clari.Create
    Op = clari.Op
    m = {  # Non trivial translations
        # TODO: populate
        "ZeroExt": (Create.zero_ext, Op.ZeroExt,),
        "SignExt": (Create.sign_ext, Op.SignExt,),
        "LShR": (Create.shift_logical_right, Op.ShiftLogicalRight,),
        "__rshift__": (Create.shift_arithmetic_right, Op.ShiftArithmeticRight,),
        "__lshift__": (Create.shift_l, Op.ShiftLeft,),
    }
    # Types
    types = ["Bool", "BV", "FP", "String", "VS"]
    fname = lambda p, t: f"{p}_{t}".lower()
    get_func = lambda t, p: (getattr(Create, fname(p, t)), getattr(Op, p))
    m.update({(i + "V"): get_func(i, "Literal") for i in types})
    m.update({(i + "S"): get_func(i, "Symbol") for i in types})
    return m

_ctor_map = _gen_ctor_type_map()

# Trivial lookups can work if the name is tweaked
_conv_map = {
    # TODO: populate
    "__ne__": "neq",
    "__mod__": "UMod",
    "__floordiv__": "UDiv",
    "__gt__": "UGT",
    "__ge__": "UGE",
    "__lt__": "ULT",
    "__le__": "ULE",
}

def _gen_op_map():
    def _op_try(op_t):
        tn = op_t.op_name()
        name = '__' + tn.lower() + '__'
        try: # Try as magic first, fallback to name if not magic
            _ = _gen_ctor_type_map(name)
            return name
        except AttributeError:
            return tn
    op_m = defaultdict(_op_try)
    op_to_py_op = {
        # TODO: populate
        clari.Op.Neq : "__ne__",
        clari.Op.If : "If",
    }
    op_m.update(op_to_py_op)
    return op_m

_op_map = _gen_op_map()

# Exports

def py_op_to_ctor_type(real_py_op):
    if real_py_op in _ctor_map:
        return _ctor_map[real_py_op]
    py_op = _conv_map[real_py_op] if real_py_op in _conv_map else real_py_op
    # Find type
    def _t(py_op, Op):
        cap = lambda x: x[0].upper() + x[1:]
        re_cap = lambda m: cap(m.group()[1:])
        opts = [cap(py_op.replace("__", "")), re.sub("_([A-Za-z])", re_cap, py_op)]
        for k in ('Signed', 'Unsigned',):
            if py_op.startswith(k[0]):
                opts.append(py_op[1:] + k)
        for op_n in opts:
            if hasattr(Op, op_n):
                return getattr(Op, op_n)
    # Find ctor
    def _f(py_op, Create):
        guess1 = py_op.replace("__", "").lower()
        opts = [guess1, guess1 + '_']
        for k in ('signed', 'unsigned',):
            if py_op.startswith(k[0].upper()):
                opts.append(f"{py_op[1:]}_{k}".lower())
        for fn in opts:
            if hasattr(Create, fn):
                return getattr(Create, fn)
    # Wrapper
    def _try_ns(py_op, x):
        if not py_op.startswith(x):
            return None, None
        c = getattr(clari.Create, x.upper())
        o = getattr(clari.Op, x.upper())
        r = _f(py_op, c), _t(py_op, o)
        if not all(r):
            r = _f(py_op[len(x):], c), _t(py_op[len(x):], o)
        return r

    # Try namespaces
    r = _try_ns(py_op, "fp")
    if all(r):
        return r
    r = _try_ns(py_op, "string")
    if all(r):
        return r
    r = _f(py_op, clari.Create), _t(py_op, clari.Op)
    if not all(r):
        raise RuntimeError(f"Could not translate op {real_py_op} to C++")
    return r


def expr_op_type_pair_to_py_op(expr_t, op_t):
    is_lit = expr_t is clari.Op.Literal
    if is_lit or expr_t is clari.Op.Symbol:
        return expr_t.type_name() + ('V' if is_lit else 'S')
    return _op_map[op_t]

def expr_to_py_op(expr):
    return expr_op_type_pair_to_py_op(type(expr), type(expr.op))


from_rm = {
    'RM_RNE' : clari.Mode.FP.Rounding.NearestTiesEven,
    'RM_RNA' : clari.Mode.FP.Rounding.NearestTiesAwayFromZero,
    'RM_RTZ' : clari.Mode.FP.Rounding.TowardsZero,
    'RM_RTP' : clari.Mode.FP.Rounding.TowardsPositiveInf,
    'RM_RTN' : clari.Mode.FP.Rounding.TowardsNegativeInf,
}

def create(op, args, *, length=None):
    ctor, t = py_op_to_ctor_type(op)
    # Fix args
    if op == "BoolS":
        args = (args[0],)
    elif op in {'BVS', 'FPS', 'VSS', 'StringS'}:
        assert length is not None, f"{op} should have a length"
        args = (args[0], length,)
    elif op == "FPV":
        assert length is not None, f"{op} should have a length"
        args = [args[0], length]
    else:
        def fx(arg):
            try:
                return arg._native # @property might create attr, no hasattr check
            except AttributeError:
                if issubclass(type(arg), Enum):
                    return from_rm[arg.value]
                return arg

        args = [fx(i) for i in args]
    # Order args
    if issubclass(t, clari.Op.AbstractFlat):
        args = (args,)
    elif issubclass(t, clari.Op.UIntBinary):
        args = args[::-1]
    elif issubclass(t, clari.Op.FP.ModeBinary):
        args = args[1:] + [args[0]]
    # Call ctor:
    return ctor(*args)

__all__ = ("py_op_to_ctor_type", "expr_op_type_pair_to_py_op", "expr_to_py_op", "from_rm",)