from .clari_setup import clari

from collections import defaultdict
from enum import Enum
import re

# Note: we do not make things on import!
# LegacySetup may change functions!
# We instead expose an init function

def _bvv_wrapper(a1, bl, *args):
    a1 %= (2**bl) # TODO: maybe move to C++?
    if a1 >= 2**64:
        a1 = str(a1)
    return clari.Create.literal_bv(a1, bl, *args)


def _gen_ctor_type_map():
    Create = clari.Create
    Op = clari.Op
    m = {  # Non trivial translations
        "ZeroExt": (Create.zero_ext, Op.ZeroExt,),
        "SignExt": (Create.sign_ext, Op.SignExt,),
        "LShR": (Create.shift_logical_right, Op.ShiftLogicalRight,),
        "__rshift__": (Create.shift_arithmetic_right, Op.ShiftArithmeticRight,),
        "__lshift__": (Create.shift_l, Op.ShiftLeft,),

        "fpToUBV": (Create.FP.to_bv_unsigned, Op.FP.ToBVUnsigned),
        "fpToIEEEBV": (Create.FP.to_ieee_bv, Op.FP.ToIEEEBV),

        "IntToStr": (Create.String.from_int, Op.String.FromInt,),
    }
    # Types
    types = ["Bool", "BV", "FP", "String", "VS"]
    fname = lambda p, t: f"{p}_{t}".lower()
    get_func = lambda t, p: (getattr(Create, fname(p, t)), getattr(Op, p))
    m.update({(i + "V"): get_func(i, "Literal") for i in types})
    m.update({(i + "S"): get_func(i, "Symbol") for i in types})
    m["BVV"] = (_bvv_wrapper, m["BVV"][1])
    return m

# Trivial lookups can work if the name is tweaked
_conv_map = {
    "__ne__": "neq",
    "__mod__": "UMod",
    "__floordiv__": "UDiv",
    "__gt__": "UGT",
    "__ge__": "UGE",
    "__lt__": "ULT",
    "__le__": "ULE",

    "fpIsNaN": "fpIs_nan",

    "StrConcat": "Concat",
    "StrIndexOf": "StrIndex_Of",
    "StrIsDigit": "StrIs_Digit",
    "StrPrefixOf": "StrPrefix_Of",
    "StrSuffixOf": "StrSuffix_Of",
    "StrToInt": "StrTo_Int",
    "StrSubstr": "StrSub_string",
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

def _bimap(*x):
    return {i: k for i, k in x}, {k: i for i, k in x},

def _gen_rms():
    return _bimap(
        ('RM_RNE', clari.Mode.FP.Rounding.NearestTiesEven,),
        ('RM_RNA', clari.Mode.FP.Rounding.NearestTiesAwayFromZero,),
        ('RM_RTZ', clari.Mode.FP.Rounding.TowardsZero,),
        ('RM_RTP', clari.Mode.FP.Rounding.TowardsPositiveInf,),
        ('RM_RTN', clari.Mode.FP.Rounding.TowardsNegativeInf,),
    )

def _py_op_to_ctor_type(real_py_op):
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
    def _try_ns(py_op, x, ns):
        if not py_op.startswith(x):
            return None, None
        c = getattr(clari.Create, ns)
        o = getattr(clari.Op, ns)
        r = _f(py_op, c), _t(py_op, o)
        if not all(r):
            r = _f(py_op[len(x):], c), _t(py_op[len(x):], o)
        return r

    # Try namespaces
    r = _try_ns(py_op, "fp", "FP")
    if all(r):
        return r
    r = _try_ns(py_op, "Str", "String")
    # r = _try_ns(py_op, "string")
    if all(r):
        return r
    r = _f(py_op, clari.Create), _t(py_op, clari.Op)
    if not all(r):
        raise RuntimeError(f"Could not translate op {real_py_op} to C++")
    return r

_ctor_map = None
_op_map = None
_rms = None

# Exports

def conv_rm(x):
    return _rms[1 if isinstance(x, clari.Mode.FP.Rounding) else 0][x]

def init():
    global _op_map
    global _ctor_map
    global _rms
    _op_map = _gen_op_map()
    _ctor_map = _gen_ctor_type_map()
    _rms = _gen_rms()


def expr_op_type_pair_to_py_op(expr_t, op_t):
    is_lit = expr_t is clari.Op.Literal
    if is_lit or expr_t is clari.Op.Symbol:
        return expr_t.type_name() + ('V' if is_lit else 'S')
    return _op_map[op_t]

def expr_to_py_op(expr):
    return expr_op_type_pair_to_py_op(type(expr), type(expr.op))


def create(op, args, *, length=None):
    # Get ctor and type
    if op == "fpToFP":
        if len(args) == 2:
            ctor = clari.Create.FP.from_not_2s_complement_bv
            t = clari.Op.FP.FromNot2sComplementBV
        elif hasattr(args[1], 'sort'):
            ctor = clari.Create.FP.from_fp
            t = clari.Op.FP.FromFP
        else:
            ctor = clari.Create.FP.from_2s_complement_signed
            t = clari.Op.FP.From2sComplementSigned
    else:
        ctor, t = _py_op_to_ctor_type(op)

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
                if isinstance(arg, Enum):
                    return conv_rm(arg.value)
                return arg

        args = [fx(i) for i in args]
    # Order args
    if issubclass(t, clari.Op.AbstractFlat):
        args = (args,)
    elif issubclass(t, clari.Op.UIntBinary) and not op.startswith("Str"):
        args = args[::-1]
    elif issubclass(t, clari.Op.FP.ModeBinary):
        args = args[1:] + [args[0]]
    # Call ctor:
    return ctor(*args)

__all__ = ("init", "expr_op_type_pair_to_py_op", "expr_to_py_op", "conv_rm",)