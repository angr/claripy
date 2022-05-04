from .clari_setup import clari

from collections import defaultdict

print(dir(clari.Create))

def _gen_py_op_to_ctor():
    # Add default (handles magic methods and such)
    m = defaultdict(lambda name: getattr(clari.Create, name))
    m.update({  # Non magic methods
        # TODO: populate
        "If": clari.Create.if_,
    })
    # Types
    types = ["Bool", "BV", "FP", "String", "VS"]
    get_func = lambda t, p: getattr(clari.Create, f"{p}_{t.lower()}")
    m.update({(i + "V"): get_func(i, "literal") for i in types})
    m.update({(i + "S"): get_func(i, "symbol") for i in types})
    return m

def _gen_op_map():
    def _op_try(op_t):
        tn = op_t.op_name()
        name = '__' + tn.lower() + '__'
        try: # Try as magic first, fallback to name if not magic
            _ = py_op_to_ctor[name]
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

def expr_op_type_pair_to_py_op(expr_t, op_t):
    is_lit = expr_t is clari.Op.Literal
    if is_lit or expr_t is clari.Op.Symbol:
        return expr_t.type_name() + ('V' if is_lit else 'S')
    return _op_map[op_t]

def expr_to_py_op(expr):
    return expr_op_type_pair_to_py_op(type(expr), type(expr.op))

py_op_to_ctor = _gen_py_op_to_ctor()

__all__ = ("py_op_to_ctor", "expr_op_type_pair_to_py_op", "expr_to_py_op")