"""
Methods and classes representing and manipulating concrete and symbolic
(frontend) boolean values.
"""

import logging
l = logging.getLogger('claripy.ast.bool')

from .base import Base, _make_name, make_op, _type_fixers

_boolv_cache = dict()

# This is a hilarious hack to get around some sort of bug in z3's python bindings, where
# under some circumstances stuff gets destructed out of order
def cleanup():
    """
    Clears the boolean value cache.
    """
    global _boolv_cache #pylint:disable=global-variable-not-assigned
    del _boolv_cache
import atexit
atexit.register(cleanup)

class Bool(Base):
    """
    Base class specialized to boolean values.
    """
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

def BoolS(name, explicit_name=None, filters=None):
    """
    Creates a boolean symbol (i.e., a variable).

    :param name:            The name of the symbol
    :param explicit_name:   If False, an identifier is appended to the name to ensure uniqueness.

    :return:                A Bool object representing this symbol.
    """
    n = _make_name(name, -1, False if explicit_name is None else explicit_name)
    return Bool(get_structure('BoolS', (n,)), filters=filters, _eager=False)._deduplicate()._apply_filters()

# why the fuck does this have to be so high up? with this lower, the reference to backends fails,
# although it doesn't do that when this is put below other module-level functions that reference
# backends
from ..backend_manager import backends

def BoolV(val, filters=None):
    """
    Creates a concrete boolean.

    :param val: Value to be placed in boolean.
    """
    if filters is None:
        return true if val else false
    else:
        return Bool(get_structure('BoolV', (val,)), filters=filters)._deduplicate()._apply_filters()

_type_fixers[bool] = lambda b,r: true if b else false
_type_fixers[Bool] = lambda b,r: b

#
# Bound operations
#

Bool.__eq__ = make_op('__eq__', (Bool, Bool), Bool)
Bool.__ne__ = make_op('__ne__', (Bool, Bool), Bool)
Bool.intersection = make_op('intersection', (Bool, Bool), Bool)

#
# Unbound operations
#

from .bv import BVS, BV
from .fp import FP

_If_bool = make_op('If', (Bool, Bool, Bool), Bool)
_If_bv = make_op('If', (Bool, BV, BV), BV)
_If_fp = make_op('If', (Bool, FP, FP), FP)
def If(c, t, f):
    """
    Creates an if-then-else condition after pushing around the types of things
    a little bit. Does some trivial simplifications as well.

    :param c: Condition of the ITE.
    :param t: True branch.
    :param f: False branch.
    """
    # the coercion here is strange enough that we'll just implement it manually
    tt = type(t)
    tf = type(f)

    # figure out our Base-subclass (bc)
    bc, nbc = (tt, tf) if issubclass(tt, Base) else (tf, tt)
    if not issubclass(bc, Base):
        raise ClaripyTypeError("At least one of the clauses to If() must be an AST.")
    if issubclass(nbc, Base):
        if bc is not nbc:
            raise ClaripyTypeError("If() received two different AST types for its true and false value.")
        elif t.length != f.length:
            raise ClaripyTypeError("True and false value arguments to If() must have the same length")
        else:
            ct, cf = t, f
    else:
        try:
            if tt is nbc: # convert t
                ct, cf = _type_fixers[nbc](t, f), f
            else: # convert f
                ct, cf = t, _type_fixers[nbc](f, t)
        except KeyError:
            raise ClaripyTypeError("Can't convert {} to {}".format(nbc, bc))

    if bc is BV:
        return _If_bv(c, ct, cf)
    elif bc is Bool:
        return _If_bool(c, ct, cf)
    elif bc is FP:
        return _If_fp(c, ct, cf)
    else:
        raise ClaripyTypeError("Unsupported type %s for true and false value arguments to If()" % bc.__name__)

And = make_op('And', Bool, Bool)
Or = make_op('Or', Bool, Bool)
Not = make_op('Not', (Bool,), Bool)

def is_true(e, exact=None): #pylint:disable=unused-argument
    """
    Queries the quick backends to check if `e` can be shown to be trivially
    true.
    """
    for b in backends._quick_backends:
        try: return b.is_true(e)
        except BackendError: pass

    l.debug("Unable to tell the truth-value of this expression")
    return False

def is_false(e, exact=None): #pylint:disable=unused-argument
    """
    Queries the quick backends to check if `e` can be shown to be trivially
    false.
    """
    for b in backends._quick_backends:
        try: return b.is_false(e)
        except BackendError: pass

    l.debug("Unable to tell the truth-value of this expression")
    return False

def ite_dict(i, d, default):
    """
    Forms a sort of switch statement from ITE statements, using a dict.

    :param i: The value we are switching on.
    :param d: Dictionary of the possible cases as keys and the corresponding
              result value as the values.
    :param default: The default AST if there is no match.

    :returns: The appropriate AST representing the switch statement.
    """
    return ite_cases([ (i == c, v) for c,v in d.items() ], default)

def ite_cases(cases, default):
    """
    Forms a nested sequence of ITE expressions from a list of tuples of
    (condition, value).

    :param cases: List of tuples of condition and result value.
    :param default: Default value if none of the conditions hold.

    :returns: A series of nested ITE expressions, in the order given in `cases`.
    """
    sofar = default
    for c,v in reversed(cases):
        sofar = If(c, v, sofar)
    return sofar

def constraint_to_si(expr):
    """
    Convert a constraint to a strided interval if possible using the VSA backend.

    :param expr: Constraint to convert.
    :returns: Tuple of (bool, list) where the first is true if the constraint
              can be convert to a strided interval, and the latter is a list
              of tuples of (original AST, replacement BVS).
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

from ..errors import ClaripyTypeError, BackendError
from .structure import get_structure, _true_structure, _false_structure
true = Bool(_true_structure)._deduplicate()
false = Bool(_false_structure)._deduplicate()
