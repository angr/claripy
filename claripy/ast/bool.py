import logging
l = logging.getLogger('claripy.ast.bool')

from ..ast.base import Base

class Bool(Base):
    @staticmethod
    def _from_bool(like, val): #pylint:disable=unused-argument
        return BoolI(val)

    def is_true(self):
        '''
        Returns True if 'self' can be easily determined to be True.
        Otherwise, return False. Note that the AST *might* still be True (i.e.,
        if it were simplified via Z3), but it's hard to quickly tell that.
        '''
        return is_true(self)

    def is_false(self):
        '''
        Returns True if 'self' can be easily determined to be False.
        Otherwise, return False. Note that the AST *might* still be False (i.e.,
        if it were simplified via Z3), but it's hard to quickly tell that.
        '''
        return is_false(self)

    def _simplify_And(self):
        if any(a.is_false() for a in self.args):
            return BoolI(False)
        else:
            new_args = [ a.simplified for a in self.args if not a.is_true() ]
            if len(new_args) == 0:
                return BoolI(True)
            else:
                return Bool(self.op, new_args)

    def _simplify_Or(self):
        if any(a.is_true() for a in self.args):
            return BoolI(True)
        else:
            new_args = [ a.simplified for a in self.args if not a.is_false() ]
            if len(new_args) == 0:
                return BoolI(False)
            else:
                return Bool(self.op, new_args)

def BoolI(model, **kwargs):
    return Bool('I', (model,), **kwargs)

def BoolVal(val):
    return BoolI(val, variables=set(), symbolic=False, eager=True)

#
# some standard ASTs
#

true = BoolVal(True)
false = BoolVal(False)

#
# Bound operations
#

from .. import operations

Bool.__eq__ = operations.op('__eq__', (Bool, Bool), Bool)
Bool.__ne__ = operations.op('__ne__', (Bool, Bool), Bool)

#
# Unbound operations
#

def If(*args):
    # the coercion here is strange enough that we'll just implement it manually
    if len(args) != 3:
        raise ClaripyOperationError("invalid number of args passed to If")

    args = list(args)

    if isinstance(args[0], bool):
        args[0] = BoolI(args[0], variables=frozenset(), symbolic=False, eager=True)

    ty = None
    if isinstance(args[1], Base):
        ty = type(args[1])
    elif isinstance(args[2], Base):
        ty = type(args[2])
    else:
        raise ClaripyTypeError("true/false clause of If must have bearable types")

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
        return args[1].make_like(args[1].op, args[1].args,
                                 variables=(args[1].variables | args[0].variables),
                                 symbolic=args[1].symbolic)
    elif is_false(args[0]):
        return args[2].make_like(args[2].op, args[2].args,
                                 variables=(args[2].variables | args[0].variables),
                                 symbolic=args[2].symbolic)

    if issubclass(ty, Bits):
        return ty('If', tuple(args), length=args[1].length)
    else:
        return ty('If', tuple(args)).reduced

And = operations.op('And', Bool, Bool, bound=False)
Or = operations.op('Or', Bool, Bool, bound=False)
Not = operations.op('Not', (Bool,), Bool, bound=False)

def is_true(e):
    for b in _all_backends:
        try: return b.is_true(b.convert(e))
        except BackendError: pass

    l.debug("Unable to tell the truth-value of this expression")
    return False

def is_false(e):
    for b in _all_backends:
        try: return b.is_false(b.convert(e))
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
    '''
    Convert a constraint to SI if possible
    :param expr:
    :return:
    '''

    satisfiable = True
    replace_list = [ ]

    satisfiable, replace_list = _all_backends[1].constraint_to_si(expr)

    # Make sure the replace_list are all ast.bvs
    for i in xrange(len(replace_list)):
        ori, new = replace_list[i]
        if not isinstance(new, Base):
            new = BVI(new, variables={ new.name }, symbolic=False, length=new._bits, eager=False)
            replace_list[i] = (ori, new)

    return satisfiable, replace_list

from .. import _all_backends
from ..errors import ClaripyOperationError, ClaripyTypeError, BackendError
from .bits import Bits
from .bv import BVI
