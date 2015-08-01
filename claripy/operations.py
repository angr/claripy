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

def reverse_simplifier(*args):
    if args[0].op == 'Reverse':
        return args[0].args[0]

def and_simplifier(*args):
    if len(args) == 1:
        return args[0]

def or_simplifier(*args):
    if len(args) == 1:
        return args[0]

def concat_simplifier(*args):
    if len(args) == 1:
        return args[0]

simplifiers = {
    'Reverse': reverse_simplifier,
    'And': and_simplifier,
    'Or': or_simplifier,
    'Concat': concat_simplifier
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
