import logging
l = logging.getLogger('claripy.ast.bool')

from ..ast.base import Base, _make_name

_boolv_cache = dict()

# This is a hilarious hack to get around some sort of bug in z3's python bindings, where
# under some circumstances stuff gets destructed out of order
def cleanup():
    global _boolv_cache #pylint:disable=global-variable-not-assigned
    del _boolv_cache
import atexit
atexit.register(cleanup)

class Bool(Base):
    @staticmethod
    def _from_bool(like, val): #pylint:disable=unused-argument
        return BoolV(val)

    def is_true(self):
        """
        Returns True if 'self' can be easily determined to be True. Otherwise, return False. Note that the AST *might*
        still be True (i.e., if it were simplified via Z3), but it's hard to quickly tell that.
        """
        return is_true(self)

    def is_false(self):
        """
        Returns True if 'self' can be easily determined to be False. Otherwise, return False. Note that the AST *might*
        still be False (i.e., if it were simplified via Z3), but it's hard to quickly tell that.
        """
        return is_false(self)


def BoolS(name, explicit_name=None):
    """
    Creates a boolean symbol (i.e., a variable).

    :param name:            The name of the symbol
    :param explicit_name:   If False, an identifier is appended to the name to ensure uniqueness.

    :return:                A Bool object representing this symbol.
    """
    n = _make_name(name, -1, False if explicit_name is None else explicit_name)
    return Bool('BoolS', (n,), variables={n}, symbolic=True)

def BoolV(val):
    try: return _boolv_cache[(val)]
    except KeyError: pass
    result = Bool('BoolV', (val,))
    _boolv_cache[val] = result
    return result

#
# some standard ASTs
#

true = BoolV(True)
false = BoolV(False)

#
# Bound operations
#

from .. import operations

Bool.__eq__ = operations.op('__eq__', (Bool, Bool), Bool)
Bool.__ne__ = operations.op('__ne__', (Bool, Bool), Bool)
Bool.intersection = operations.op('intersection', (Bool, Bool), Bool)

#
# Unbound operations
#

def If(*args):
    # the coercion here is strange enough that we'll just implement it manually
    if len(args) != 3:
        raise ClaripyOperationError("invalid number of args passed to If")

    args = list(args)

    if isinstance(args[0], bool):
        args[0] = BoolV(args[0])

    ty = None
    if isinstance(args[1], Base):
        ty = type(args[1])
    elif isinstance(args[2], Base):
        ty = type(args[2])
    else:
        raise ClaripyTypeError("true/false clause of If must have bearable types")

    if isinstance(args[1], Bits) and isinstance(args[2], Bits) and args[1].length != args[2].length:
        raise ClaripyTypeError("sized arguments to If must have the same length")

    if not isinstance(args[1], ty):
        if hasattr(ty, '_from_' + type(args[1]).__name__):
            convert = getattr(ty, '_from_' + type(args[1]).__name__)
            args[1] = convert(args[2], args[1])
        else:
            raise ClaripyTypeError("can't convert {} to {}".format(type(args[1]), ty))
    if not isinstance(args[2], ty):
        if hasattr(ty, '_from_' + type(args[2]).__name__):
            convert = getattr(ty, '_from_' + type(args[2]).__name__)
            args[2] = convert(args[1], args[2])
        else:
            raise ClaripyTypeError("can't convert {} to {}".format(type(args[2]), ty))

    if is_true(args[0]):
        return args[1]
    elif is_false(args[0]):
        return args[2]

    if isinstance(args[1], Base) and args[1].op == 'If' and args[1].args[0] is args[0]:
        return If(args[0], args[1].args[1], args[2])
    if isinstance(args[1], Base) and args[1].op == 'If' and args[1].args[0] is Not(args[0]):
        return If(args[0], args[1].args[2], args[2])
    if isinstance(args[2], Base) and args[2].op == 'If' and args[2].args[0] is args[0]:
        return If(args[0], args[1], args[2].args[2])
    if isinstance(args[2], Base) and args[2].op == 'If' and args[2].args[0] is Not(args[0]):
        return If(args[0], args[1], args[2].args[1])

    if issubclass(ty, Bits):
        return ty('If', tuple(args), length=args[1].length)
    else:
        return ty('If', tuple(args))

And = operations.op('And', Bool, Bool, bound=False)
Or = operations.op('Or', Bool, Bool, bound=False)
Not = operations.op('Not', (Bool,), Bool, bound=False)

def is_true(e, exact=None): #pylint:disable=unused-argument
    for b in backends._quick_backends:
        try: return b.is_true(e)
        except BackendError: pass

    l.debug("Unable to tell the truth-value of this expression")
    return False

def is_false(e, exact=None): #pylint:disable=unused-argument
    for b in backends._quick_backends:
        try: return b.is_false(e)
        except BackendError: pass

    l.debug("Unable to tell the truth-value of this expression")
    return False

def ite_dict(i, d, default):
    return ite_cases([ (i == c, v) for c,v in d.items() ], default)

def ite_cases(cases, default):
    sofar = default
    for c,v in reversed(cases):
        sofar = If(c, v, sofar)
    return sofar

def constraint_to_si(expr):
    """
    Convert a constraint to SI if possible.

    :param expr:
    :return:
    """

    satisfiable = True
    replace_list = [ ]

    satisfiable, replace_list = backends.vsa.constraint_to_si(expr)

    # Make sure the replace_list are all ast.bvs
    for i in xrange(len(replace_list)):
        ori, new = replace_list[i]
        if not isinstance(new, Base):
            new = BVS(new.name, new._bits, min=new._lower_bound, max=new._upper_bound, stride=new._stride, explicit_name=True)
            replace_list[i] = (ori, new)

    return satisfiable, replace_list

from ..backend_manager import backends
from ..errors import ClaripyOperationError, ClaripyTypeError, BackendError
from .bits import Bits
from .bv import BVS
