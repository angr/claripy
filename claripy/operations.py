def op(name, arg_types, return_type, extra_check=None, calc_length=None, self_is_clrp=False, do_coerce=True):
    def _op(self, *args):
        if self_is_clrp:
            clrp = self
        else:
            clrp = self._claripy
            args = (self,) + args

        if isinstance(arg_types, tuple):
            if len(args) != len(arg_types):
                raise ClaripyTypeError("Operation {} takes exactly "
                                       "{} arguments ({} given)".format(name, len(arg_types), len(args)))

            # heuristically, this works!
            thing = None
            for arg, argty in zip(args, arg_types):
                if isinstance(arg, argty):
                    thing = arg

            for i, (arg, argty) in enumerate(zip(args, arg_types)):
                if not isinstance(arg, argty):
                    if do_coerce and hasattr(argty, '_from_' + type(arg).__name__):
                        convert = getattr(argty, '_from_' + type(arg).__name__)
                        args = tuple(convert(clrp, thing, arg) if j == i else a for (j, a) in enumerate(args))
                    else:
                        return NotImplemented
                        # raise ClaripyTypeError("Operation {} requires type {} for arg #{}, got {}"
                        #                        .format(name, argty.__name__, i, type(arg).__name__))
        elif isinstance(arg_types, type):
            argty = arg_types

            # heuristically, this works!
            thing = None
            for arg in args:
                if isinstance(arg, argty):
                    thing = arg

            for i, arg in enumerate(args):
                if not isinstance(arg, argty):
                    if do_coerce and hasattr(argty, '_from_' + type(arg).__name__):
                        convert = getattr(argty, '_from_' + type(arg).__name__)
                        args = tuple(convert(clrp, thing, arg) if j == i else a for (j, a) in enumerate(args))
                    else:
                        return NotImplemented
                    # raise ClaripyTypeError("Operation {} requires type {} for arg #{}, got {}"
                    #                        .format(name, arg_types.__name__, i, type(arg).__name__))
        else:
            raise ClaripyOperationError("op {} got weird arg_types".format(name))

        if extra_check is not None:
            success, msg = extra_check(*args)
            if not success:
                raise ClaripyOperationError(msg)

        kwargs = {}
        if calc_length is not None:
            kwargs['length'] = calc_length(*args)

        return return_type(clrp, name, args, **kwargs)

    _op.calc_length = calc_length
    return _op

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
    'UGE', 'ULE', 'UGT', 'ULT',
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

inverse_operations = {
    '__eq__': '__ne__',
    '__ne__': '__eq__'
}

length_same_operations = expression_arithmetic_operations | backend_bitwise_operations | expression_bitwise_operations | backend_other_operations | expression_set_operations | {'Reversed'}
length_none_operations = backend_comparator_operations | expression_comparator_operations | backend_boolean_operations
length_change_operations = backend_bitmod_operations
length_new_operations = backend_creation_operations

#
# Reversibility
#

not_invertible = {'Identical', 'union'}
reverse_distributable = { 'widen', 'union', 'intersection',
    '__invert__', '__or__', '__ror__', '__and__', '__rand__', '__xor__', '__rxor__',
}

from .errors import ClaripyTypeError, ClaripyOperationError
