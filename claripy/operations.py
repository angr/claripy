import itertools
si_counter = itertools.count()

def op(name, arg_types, return_type, extra_check=None, calc_length=None, do_coerce=True, bound=True): #pylint:disable=unused-argument
    if type(arg_types) in (tuple, list): #pylint:disable=unidiomatic-typecheck
        expected_num_args = len(arg_types)
    elif type(arg_types) is type: #pylint:disable=unidiomatic-typecheck
        expected_num_args = None
    else:
        raise ClaripyOperationError("op {} got weird arg_types".format(name))

    def _type_fixer(args):
        num_args = len(args)
        if expected_num_args is not None and num_args != expected_num_args:
            raise ClaripyTypeError("Operation {} takes exactly "
                                   "{} arguments ({} given)".format(name, len(arg_types), len(args)))

        if type(arg_types) is type: #pylint:disable=unidiomatic-typecheck
            actual_arg_types = (arg_types,) * num_args
        else:
            actual_arg_types = arg_types
        matches = [ isinstance(arg, argty) for arg,argty in zip(args, actual_arg_types) ]

        # heuristically, this works!
        thing = args[matches.index(True)] if True in matches else None

        for arg, argty, matches in zip(args, actual_arg_types, matches):
            if not matches:
                if do_coerce and hasattr(argty, '_from_' + type(arg).__name__):
                    convert = getattr(argty, '_from_' + type(arg).__name__)
                    yield convert(thing, arg)
                else:
                    yield NotImplemented
                    return
            else:
                yield arg

    def _op(*args):
        fixed_args = tuple(_type_fixer(args))
        for i in fixed_args:
            if i is NotImplemented:
                return NotImplemented

        if extra_check is not None:
            success, msg = extra_check(*fixed_args)
            if not success:
                raise ClaripyOperationError(msg)

        if name in simplifiers:
            simp = simplifiers[name](*fixed_args)
            if simp is not None:
                return simp

        kwargs = {}
        if calc_length is not None:
            kwargs['length'] = calc_length(*fixed_args)

        if name in preprocessors:
            args, kwargs = preprocessors[name](*args, **kwargs)

        if any(any(v.startswith('SI') for v in a.variables) for a in args if hasattr(a, 'variables')):
            kwargs['add_variables'] = frozenset(('SI_%d' % next(si_counter),))

        return return_type(name, fixed_args, **kwargs)

    _op.calc_length = calc_length
    return _op

#
# Extra processors
#

def preprocess_intersect(*args, **kwargs):
    new_name = 'SI_%d' % next(si_counter)
    kwargs['add_variables'] = frozenset((new_name,))
    return args, kwargs

def preprocess_union(*args, **kwargs):
    new_name = 'SI_%d' % next(si_counter)
    kwargs['add_variables'] = frozenset((new_name,))
    return args, kwargs

preprocessors = {
    'union': preprocess_union,
    'intersection': preprocess_intersect
}

#
# Simplifiers
#

def if_simplifier(cond, if_true, if_false):
    if cond.reduced.is_true():
        return if_true.reduced

    if cond.reduced.is_false():
        return if_false.reduced

def concat_simplifier(*args):

    if len(args) == 1:
        return args[0]

    orig_args = args
    args = list(args)
    #length = sum(arg.length for arg in args)
    simplified = False

    if any(a.symbolic for a in args):
        i = 1
        while i < len(args):
            previous = args[i-1]
            current = args[i]
            if not (previous.symbolic or current.symbolic):
                args[i-1:i+1] = (ast.all_operations.Concat(previous, current).reduced,)
            else:
                i += 1

        if len(args) < len(orig_args):
            simplified = True

    i = 0
    while i < len(args):
        current = args[i]
        if current.op == 'Concat':
            simplified = True
            args[i:i+1] = current.args
            i += len(current.args)
        else:
            i += 1

    # if any(a.op == 'Reverse' for a in args):
    #     simplified = True
    #     args = [a.reversed for a in args]

    if simplified:
        return ast.all_operations.Concat(*args)

    return

def rshift_simplifier(val, shift):
    if (shift == 0).is_true():
        return val

def lshift_simplifier(val, shift):
    if (shift == 0).is_true():
        return val

SIMPLE_OPS = ('Concat', 'SignExt', 'ZeroExt')

def eq_simplifier(a, b):
    # TODO: all these ==/!= might really slow things down...
    if a.op == 'If':
        if a.args[1] is b and ast.all_operations.is_true(a.args[2] != b):
            # (If(c, x, y) == x, x != y) -> c
            return a.args[0]
        elif a.args[2] is b and ast.all_operations.is_true(a.args[1] != b):
            # (If(c, x, y) == y, x != y) -> !c
            return ast.all_operations.Not(a.args[0])
        # elif a._claripy.is_true(a.args[1] == b) and a._claripy.is_true(a.args[2] == b):
        #     return a._claripy.true
        # elif a._claripy.is_true(a.args[1] != b) and a._claripy.is_true(a.args[2] != b):
        #     return a._claripy.false

    if b.op == 'If':
        if b.args[1] is a and ast.all_operations.is_true(b.args[2] != b):
            # (x == If(c, x, y)) -> c
            return b.args[0]
        elif b.args[2] is a and ast.all_operations.is_true(b.args[1] != a):
            # (y == If(c, x, y)) -> !c
            return ast.all_operations.Not(b.args[0])
        # elif b._claripy.is_true(b.args[1] == a) and b._claripy.is_true(b.args[2] == a):
        #     return b._claripy.true
        # elif b._claripy.is_true(b.args[1] != a) and b._claripy.is_true(b.args[2] != a):
        #     return b._claripy.false

    if (a.op in SIMPLE_OPS or b.op in SIMPLE_OPS) and a.length > 1 and a.length == b.length:
        for i in xrange(a.length):
            a_bit = a[i:i]
            if a_bit.symbolic:
                break

            b_bit = b[i:i]
            if b_bit.symbolic:
                break

            if ast.all_operations.is_false(a_bit == b_bit):
                return ast.all_operations.false

def ne_simplifier(a, b):
    if a.op == 'If':
        if a.args[2] is b and ast.all_operations.is_true(a.args[1] != b):
            # (If(c, x, y) == x, x != y) -> c
            return a.args[0]
        elif a.args[1] is b and ast.all_operations.is_true(a.args[2] != b):
            # (If(c, x, y) == y, x != y) -> !c
            return ast.all_operations.Not(a.args[0])
        # elif a._claripy.is_true(a.args[1] == b) and a._claripy.is_true(a.args[2] == b):
        #     return a._claripy.false
        # elif a._claripy.is_true(a.args[1] != b) and a._claripy.is_true(a.args[2] != b):
        #     return a._claripy.true

    if b.op == 'If':
        if b.args[2] is a and ast.all_operations.is_true(b.args[1] != a):
            # (x == If(c, x, y)) -> c
            return b.args[0]
        elif b.args[1] is a and ast.all_operations.is_true(b.args[2] != a):
            # (y == If(c, x, y)) -> !c
            return ast.all_operations.Not(b.args[0])
        # elif b._claripy.is_true(b.args[1] != a) and b._claripy.is_true(b.args[2] != a):
        #     return b._claripy.true
        # elif b._claripy.is_true(b.args[1] == a) and b._claripy.is_true(b.args[2] == a):
        #     return b._claripy.false

    if (a.op == SIMPLE_OPS or b.op in SIMPLE_OPS) and a.length > 1 and a.length == b.length:
        for i in xrange(a.length):
            a_bit = a[i:i]
            if a_bit.symbolic:
                break

            b_bit = b[i:i]
            if b_bit.symbolic:
                break

            if ast.all_operations.is_true(a_bit != b_bit):
                return ast.all_operations.true

def reverse_simplifier(body):
    if body.op == 'Reverse':
        return body.args[0]

    if body.length == 8:
        return body

    if body.op == 'Concat':
        if all(a.op == 'Extract' for a in body.args):
            first_ast = body.args[0].args[2]
            for i,a in enumerate(body.args):
                if not (first_ast.identical(a.args[2])
                        and a.args[0] == ((i + 1) * 8 - 1)
                        and a.args[1] == i * 8):
                    break
            else:
                upper_bound = body.args[-1].args[0]
                if first_ast.length == upper_bound + 1:
                    return first_ast
                else:
                    return first_ast[upper_bound:0]

def and_simplifier(*args):
    if len(args) == 1:
        return args[0]

    if any(a.is_true() for a in args):
        new_args = tuple(a for a in args if not a.is_true())
        if len(new_args) > 0:
            return ast.all_operations.And(*new_args)
        else:
            return ast.all_operations.true

def or_simplifier(*args):
    if len(args) == 1:
        return args[0]

    if any(a.is_false() for a in args):
        new_args = tuple(a for a in args if not a.is_false())
        if len(new_args) > 0:
            return ast.all_operations.Or(*new_args)
        else:
            return ast.all_operations.false

def not_simplifier(body):
    if body.op == '__eq__':
        return body.args[0] != body.args[1]
    elif body.op == '__ne__':
        return body.args[0] == body.args[1]

    if body.op == 'Not':
        return body.args[0]

    if body.op == 'If':
        return ast.all_operations.If(body.args[0], body.args[2], body.args[1])

    if body.op == 'SLT':
        return ast.all_operations.SGE(body.args[0], body.args[1])
    elif body.op == 'SLE':
        return ast.all_operations.SGT(body.args[0], body.args[1])
    elif body.op == 'SGT':
        return ast.all_operations.SLE(body.args[0], body.args[1])
    elif body.op == 'SGE':
        return ast.all_operations.SLT(body.args[0], body.args[1])

    if body.op == 'ULT':
        return ast.all_operations.UGE(body.args[0], body.args[1])
    elif body.op == 'ULE':
        return ast.all_operations.UGT(body.args[0], body.args[1])
    elif body.op == 'UGT':
        return ast.all_operations.ULE(body.args[0], body.args[1])
    elif body.op == 'UGE':
        return ast.all_operations.ULT(body.args[0], body.args[1])

def extract_simplifier(high, low, val):
    if val.op == 'ZeroExt':
        extending_bits = val.args[0]
        if extending_bits == 0:
            val = val.args[1]
        else:
            val = ast.all_operations.Concat(ast.all_operations.BVV(0, extending_bits), val.args[1])

    # Reverse(concat(a, b)) -> concat(Reverse(b), Reverse(a))
    # a and b must have lengths that are a multiple of 8
    if val.op == 'Reverse' and val.args[0].op == 'Concat' and all(a.length % 8 == 0 for a in val.args[0].args):
        val = ast.BV('Concat', tuple(reversed([a.reversed for a in val.args[0].args])), length=val.length)

    # Reading one byte from a reversed ast can be converted to reading the corresponding byte from the original ast
    # No Reverse is required then
    if val.op == 'Reverse' and high - low + 1 == 8 and low % 8 == 0:
        byte_pos = low / 8
        new_byte_pos = val.length / 8 - byte_pos - 1

        val = val.args[0]
        high = (new_byte_pos + 1) * 8 - 1
        low = new_byte_pos * 8

        return ast.BV('Extract', (high, low, val), length=high-low+1)

    if val.op == 'Concat':
        pos = val.length
        high_i, low_i, low_loc = None, None, None
        for i, v in enumerate(val.args):
            if high in xrange(pos - v.length, pos):
                high_i = i
            if low in xrange(pos - v.length, pos):
                low_i = i
                low_loc = low - (pos - v.length)
            pos -= v.length

        used = val.args[high_i:low_i+1]
        if len(used) == 1:
            self = used[0]
        else:
            self = ast.all_operations.Concat(*used)

        new_high = low_loc + high - low
        if new_high == self.length - 1 and low_loc == 0:
            return self
        else:
            # TODO: fallthrough
            # does this cause infinite recursion?
            if self.op != 'Concat':
                return self[new_high:low_loc]
            else:
                return ast.BV('Extract', (new_high, low_loc, self), length=(new_high - low_loc + 1))

    # this might be bad in general... not sure
    if val.op == 'If':
        return ast.all_operations.If(val.args[0], val.args[1][high:low], val.args[2][high:low])

    if val.op == 'Extract':
        _, inner_low = val.args[:2]
        new_low = inner_low + low
        new_high = new_low + (high - low)
        return (val.args[2])[new_high:new_low]

    if val.op == 'Reverse' and val.args[0].op == 'Concat' and all(a.length % 8 == 0 for a in val.args[0].args):
        val = val.make_like('Concat',
                            tuple(reversed([a.reversed for a in val.args[0].args])),
        )[high:low].simplified
        if not val.symbolic:
            return val

    # if all else fails, convert Extract(Reverse(...)) to Reverse(Extract(...))
    # if val.op == 'Reverse' and (high + 1) % 8 == 0 and low % 8 == 0:
    #     print "saw reverse, converting"
    #     inner_length = val.args[0].length
    #     try:
    #         return val.args[0][(inner_length - 1 - low):(inner_length - 1 - low - (high - low))].reversed
    #     except ClaripyOperationError:
    #         __import__('ipdb').set_trace()

    if val.op in extract_distributable:
        return ast.BV(val.op, tuple(a[high:low] for a in val.args), length=(high-low+1))


simplifiers = {
    'Reverse': reverse_simplifier,
    'And': and_simplifier,
    'Or': or_simplifier,
    'Not': not_simplifier,
    'Extract': extract_simplifier,
    'Concat': concat_simplifier,
    'If': if_simplifier,
    '__lshift__': lshift_simplifier,
    '__rshift__': rshift_simplifier,
    '__eq__': eq_simplifier,
    '__ne__': ne_simplifier,
}

#
# Length checkers
#

def length_same_check(*args):
    return all(a.length == args[0].length for a in args), "args' length must all be equal"

def basic_length_calc(*args):
    return args[0].length

def extract_check(high, low, bv):
    if high < 0 or low < 0:
        return False, "Extract high and low must be nonnegative"
    elif low > high:
        return False, "Extract low must be <= high"
    elif high >= bv.size():
        return False, "Extract bound must be less than BV size"

    return True, ""

def extract_length_calc(high, low, _):
    return high - low + 1

def ext_length_calc(ext, orig):
    return orig.length + ext

def concat_length_calc(*args):
    return sum(arg.size() for arg in args)

#
# Operation lists
#

expression_arithmetic_operations = {
    # arithmetic
    '__add__', '__radd__',
    '__div__', '__rdiv__',
    '__truediv__', '__rtruediv__',
    '__floordiv__', '__rfloordiv__',
    '__mul__', '__rmul__',
    '__sub__', '__rsub__',
    '__pow__', '__rpow__',
    '__mod__', '__rmod__',
    '__divmod__', '__rdivmod__',
    '__neg__',
    '__pos__',
    '__abs__',
}

# expression_arithmetic_operations = {
#     'Add', 'RAdd',
#     'Div', 'RDiv',
#     'TrueDiv', 'RTrueDiv',
#     'FloorDiv', 'RFloorDiv',
#     'Mul', 'RMul',
#     'Sub', 'RSub',
#     'Pow', 'RPow',
#     'Mod', 'RMod',
#     'DivMod', 'RDivMod',
#     'Neg',
#     'Pos',
#     'Abs',
# }

bin_ops = {
    '__add__', '__radd__',
    '__mul__', '__rmul__',
    '__or__', '__ror__',
    '__and__', '__rand__',
    '__xor__', '__rxor__',
}

expression_comparator_operations = {
    # comparisons
    '__eq__',
    '__ne__',
    '__ge__', '__le__',
    '__gt__', '__lt__',
}

# expression_comparator_operations = {
#     'Eq',
#     'Ne',
#     'Ge', 'Le',
#     'Gt', 'Lt',
# }

expression_bitwise_operations = {
    # bitwise
    '__invert__',
    '__or__', '__ror__',
    '__and__', '__rand__',
    '__xor__', '__rxor__',
    '__lshift__', '__rlshift__',
    '__rshift__', '__rrshift__',
}

expression_set_operations = {
    # Set operations
    'union',
    'intersection',
    'widen'
}

expression_operations = expression_arithmetic_operations | expression_comparator_operations | expression_bitwise_operations | expression_set_operations

backend_comparator_operations = {
    'SGE', 'SLE', 'SGT', 'SLT', 'UGE', 'ULE', 'UGT', 'ULT',
}

backend_bitwise_operations = {
    'RotateLeft', 'RotateRight', 'LShR', 'Reverse',
}

backend_boolean_operations = {
    'And', 'Or', 'Not'
}

backend_bitmod_operations = {
    'Concat', 'Extract', 'SignExt', 'ZeroExt'
}

backend_creation_operations = {
    'BoolVal', 'BitVec', 'BitVecVal'
}

backend_vsa_creation_operations = {
    'TopStridedInterval', 'StridedInterval', 'ValueSet', 'AbstractLocation'
}

backend_other_operations = { 'If' }

backend_operations = backend_comparator_operations | backend_bitwise_operations | backend_boolean_operations | backend_bitmod_operations | backend_creation_operations | backend_other_operations
backend_operations_vsa_compliant = backend_bitwise_operations | backend_comparator_operations | backend_boolean_operations | backend_bitmod_operations
backend_operations_all = backend_operations | backend_operations_vsa_compliant | backend_vsa_creation_operations

backend_fp_cmp_operations = {
    'fpLT', 'fpLEQ', 'fpGT', 'fpGEQ', 'fpEQ',
}

backend_fp_operations = {
    'FP', 'fpToFP', 'fpToIEEEBV', 'fpFP', 'fpToSBV', 'fpToUBV',
    'fpNeg', 'fpSub', 'fpAdd', 'fpMul', 'fpDiv', 'fpAbs'
} | backend_fp_cmp_operations

opposites = {
    '__add__': '__radd__', '__radd__': '__add__',
    '__div__': '__rdiv__', '__rdiv__': '__div__',
    '__truediv__': '__rtruediv__', '__rtruediv__': '__truediv__',
    '__floordiv__': '__rfloordiv__', '__rfloordiv__': '__floordiv__',
    '__mul__': '__rmul__', '__rmul__': '__mul__',
    '__sub__': '__rsub__', '__rsub__': '__sub__',
    '__pow__': '__rpow__', '__rpow__': '__pow__',
    '__mod__': '__rmod__', '__rmod__': '__mod__',
    '__divmod__': '__rdivmod__', '__rdivmod__': '__divmod__',

    '__eq__': '__eq__',
    '__ne__': '__ne__',
    '__ge__': '__le__', '__le__': '__ge__',
    '__gt__': '__lt__', '__lt__': '__gt__',

    #'__neg__':
    #'__pos__':
    #'__abs__':
    #'__invert__':
    '__or__': '__ror__', '__ror__': '__or__',
    '__and__': '__rand__', '__rand__': '__and__',
    '__xor__': '__rxor__', '__rxor__': '__xor__',
    '__lshift__': '__rlshift__', '__rlshift__': '__lshift__',
    '__rshift__': '__rrshift__', '__rrshift__': '__rshift__',
}

reversed_ops = {
    '__radd__': '__add__',
    '__rand__': '__and__',
    '__rdiv__': '__div__',
    '__rdivmod__': '__divmod__',
    '__rfloordiv__': '__floordiv__',
    '__rlshift__': '__lshift__',
    '__rmod__': '__mod__',
    '__rmul__': '__mul__',
    '__ror__': '__or__',
    '__rpow__': '__pow__',
    '__rrshift__': '__rshift__',
    '__rsub__': '__sub__',
    '__rtruediv__': '__truediv__',
    '__rxor__': '__xor__'
}

inverse_operations = {
    '__eq__': '__ne__',
    '__ne__': '__eq__'
}

length_same_operations = expression_arithmetic_operations | backend_bitwise_operations | expression_bitwise_operations | backend_other_operations | expression_set_operations | {'Reversed'}
length_none_operations = backend_comparator_operations | expression_comparator_operations | backend_boolean_operations | backend_fp_cmp_operations
length_change_operations = backend_bitmod_operations
length_new_operations = backend_creation_operations

#
# Reversibility
#

not_invertible = {'Identical', 'union'}
reverse_distributable = { 'widen', 'union', 'intersection',
    '__invert__', '__or__', '__ror__', '__and__', '__rand__', '__xor__', '__rxor__',
}

extract_distributable = {
    '__and__', '__rand__',
    '__or__', '__ror__',
    '__xor__', '__rxor__',
}

infix = {
    '__add__': '+',
    '__sub__': '-',
    '__mul__': '*',
    '__div__': '/',
    '__floordiv__': '/',
#    '__truediv__': 'does this come up?',
    '__pow__': '**',
    '__mod__': '%',
#    '__divmod__': "don't think this is used either",

    '__eq__': '==',
    '__ne__': '!=',
    '__ge__': '>=',
    '__le__': '<=',
    '__gt__': '>',
    '__lt__': '<',

    'UGE': '>=',
    'ULE': '<=',
    'UGT': '>',
    'ULT': '<',

    'SGE': '>=s',
    'SLE': '<=s',
    'SGT': '>s',
    'SLT': '<s',

    '__or__': '|',
    '__and__': '&',
    '__xor__': '^',
    '__lshift__': '<<',
    '__rshift__': '>>',

    'And': '&&',
    'Or': '||',

    'Concat': '..',
}

from .errors import ClaripyOperationError, ClaripyTypeError
from . import ast
