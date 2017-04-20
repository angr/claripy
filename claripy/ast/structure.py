import itertools
import logging
import weakref
import hashlib
import cPickle as pickle
import struct
import sys
import ana

_md5_unpacker = struct.Struct('2Q')
l = logging.getLogger("claripy.expressions.structure")

#
# Some helpers
#

def _inner_repr(a, **kwargs):
    if isinstance(a, ASTStructure):
        return a.repr(inner=True, **kwargs)
    else:
        return repr(a)

#
# AST Structure
#

class ASTStructure(ana.Storable):
    def __init__(self, op, args, annotations=()):
        self.op = op
        self.args = args
        self.annotations = annotations
        self._hash = None

    def __hash__(self):
        if self._hash is None:
            self._hash = self._calc_hash()
        return self._hash

    def _calc_hash(self):
        """
        Calculates the hash of an ASTStructure.
        """
        args_tup = tuple(long(a) if type(a) is int else (a if type(a) in (long, float) else hash(a)) for a in self.args)
        to_hash = (self.op, args_tup, hash(self.annotations))

        # Why do we use md5 when it's broken? Because speed is more important
        # than cryptographic integrity here. Then again, look at all those
        # allocations we're doing here... fast python is painful.
        hd = hashlib.md5(pickle.dumps(to_hash, -1)).digest()
        return _md5_unpacker.unpack(hd)[0] # 64 bits

    def __eq__(self, o):
        # special-case for BVV and BoolV
        if type(o) in (int, long, float, bool):
            if self.op in operations.backend_creation_operations:
                return self.args[0] == o
            else:
                return False

        if type(o) is not ASTStructure:
            return False

        return self is o or hash(self) == hash(o) # or (self.op == o.op and self.args == o.args and self.annotations == o.annotations)
    def __ne__(self, o):
        return not self.__eq__(o)

    @property
    def symbolic(self):
        return backends.symbolic.convert(self)
    @property
    def length(self):
        return backends.length.convert(self)

    #
    # Various structural modifications
    #

    def annotate(self, *annotations):
        return get_structure(self.op, self.args, self.annotations+annotations)

    def swap_annotations(self, annotations):
        return get_structure(self.op, self.args, annotations)

    def swap_args(self, args):
        if len(self.args) == len(args) and all(a is b for a,b in zip(self.args, args)):
            return self
        return get_structure(self.op, args, self.annotations)

    def reverse_operation(self):
        if self.op in operations.boolean_opposites:
            return get_structure(operations.boolean_opposites[self.op], self.args[::-1], self.annotations)
        else:
            raise ClaripyOperationError("Cannot reverse operation %s" % self.op)

    def replace(self, replacements, leaf_operation=None):
        """
        A helper for replace().

        :param replacements: A dictionary of hashes to their replacements.
        """
        try: return replacements[self]
        except KeyError: pass

        if leaf_operation is not None and self.op in operations.leaf_operations:
            r = _deduplicate(leaf_operation(self))
        else:
            new_args = [
                a.replace(replacements=replacements, leaf_operation=leaf_operation) if isinstance(a, ASTStructure) else a
                for a in self.args
            ]

            if any(old_a is not new_a for old_a,new_a in zip(self.args,new_args)):
                r = _deduplicate(self.swap_args(tuple(new_args)))
            else:
                r = self

        replacements[self] = r
        return r

    def canonicalize(self, var_map=None, counter=None):
        """
        Converts the structure to a canonical form (just normalizing variable names for now).

        :param var_map:    A map of variable name normalizations -- MODIFIED IN PLACE.
        :param counter: An iterator to generate normalized numbers for names.

        :returns: a tuple of (new_var_map, new_counter, new_structure)
        """

        counter = itertools.count() if counter is None else counter
        var_map = { } if var_map is None else var_map

        for v in self._recursive_leaves():
            if v not in var_map and v.op in { 'BVS', 'BoolS', 'FPS' }:
                new_name = 'cv%d' % next(counter)
                var_map[v] = v.swap_args((new_name,)+v.args[1:])

        return var_map, counter, self.replace(var_map)

    #
    # Serialization support
    #

    def _ana_getstate(self):
        """
        Support for ANA serialization.
        """
        return self.op, self.args, self.annotations, hash(self)

    def _ana_setstate(self, state):
        """
        Support for ANA deserialization.
        """
        self.op, self.args, self.annotations, self._hash = state
        _hash_cache[self._hash] = self

    def make_uuid(self, uuid=None):
        """
        This overrides the default ANA uuid with the hash of the AST. UUID is slow, and we'll soon replace it from ANA
        itself, and this will go away.

        :returns: a string representation of the AST hash.
        """
        u = getattr(self, '_ana_uuid', None)
        if u is None:
            u = str(hash(self)) if uuid is None else uuid
            ana.get_dl().uuid_cache[u] = self
            setattr(self, '_ana_uuid', u)
        return u

    #
    # Debugging
    #

    @property
    def dbg_recursive_children(self):
        for a in self.args:
            if isinstance(a, ASTStructure):
                l.debug("Yielding node %s with hash %s with %d children", a, hash(a), len(a.args))
                yield a
                for b in a.recursive_children:
                    yield b

    @property
    def dbg_recursive_leaves(self):
        return self._recursive_leaves()

    def _recursive_leaves(self, seen=None):
        leaf = all(not isinstance(a, ASTStructure) for a in self.args)
        if leaf:
            yield self
            return

        seen = set() if seen is None else seen
        for a in self.args:
            if isinstance(a, ASTStructure) and not a in seen:
                seen.add(a)
                for b in a._recursive_leaves(seen=seen):
                    yield b

    def dbg_is_looped(self, seen=None, checked=None):
        seen = set() if seen is None else seen
        checked = set() if checked is None else checked

        l.debug("Checking node with hash %s for looping", hash(self))
        if self in seen:
            return self
        elif self in checked:
            return False
        else:
            seen.add(self)

            for a in self.args:
                if not isinstance(a, ASTStructure):
                    continue

                r = a.dbg_is_looped(seen=set(seen), checked=checked)
                if r is not False:
                    return r

            checked.add(self)
            return False

    @property
    def depth(self):
        """
        The depth of this AST. For example, an AST representing (a+(b+c)) would have a depth of 2.
        """
        return backends.depth.convert(self)

    #
    # String representation
    #

    def __repr__(self):
        return self.repr(inner=True)

    def repr(self, inner=False, max_depth=None, explicit_length=False):
        if max_depth is not None and max_depth <= 0:
            return '...'

        if max_depth is not None:
            max_depth -= 1

        try:
            if self.op in operations.reversed_ops:
                op = operations.reversed_ops[self.op]
                args = self.args[::-1]
            else:
                op = self.op
                args = self.args

            if op == 'BVS' and inner:
                value = args[0]
            elif op == 'BVS':
                value = "%s" % args[0]
                extras = [ ]
                if args[2] is not None:
                    extras.append("min=%s" % args[1])
                if args[3] is not None:
                    extras.append("max=%s" % args[2])
                if args[4] is not None:
                    extras.append("stride=%s" % args[3])
                if args[5] is True:
                    extras.append("UNINITIALIZED")
                if len(extras) != 0:
                    value += "{" + ", ".join(extras) + "}"
            elif op == 'BoolV':
                value = str(args[0])
            elif op == 'BVV':
                if self.args[0] is None:
                    value = '!'
                elif self.args[1] < 10:
                    value = format(self.args[0], '')
                else:
                    value = format(self.args[0], '#x')
                value += ('#' + str(backends.length.convert(self))) if explicit_length else ''
            elif op == 'If':
                value = 'if {} then {} else {}'.format(_inner_repr(args[0], max_depth=max_depth),
                                                       _inner_repr(args[1], max_depth=max_depth),
                                                       _inner_repr(args[2], max_depth=max_depth))
                if inner:
                    value = '({})'.format(value)
            elif op == 'Not':
                value = '!{}'.format(_inner_repr(args[0], max_depth=max_depth))
            elif op == 'Extract':
                value = '{}[{}:{}]'.format(_inner_repr(args[2], max_depth=max_depth), args[0], args[1])
            elif op == 'ZeroExt':
                value = '0#{} .. {}'.format(args[0], _inner_repr(args[1], max_depth=max_depth))
                if inner:
                    value = '({})'.format(value)
            elif op == 'Concat':
                value = ' .. '.join(_inner_repr(a, explicit_length=True, max_depth=max_depth) for a in self.args)
            elif len(args) == 2 and op in operations.infix:
                value = '{} {} {}'.format(_inner_repr(args[0], max_depth=max_depth),
                                          operations.infix[op],
                                          _inner_repr(args[1], max_depth=max_depth))
                if inner:
                    value = '({})'.format(value)
            else:
                value = "{}({})".format(op,
                                        ', '.join(_inner_repr(a, max_depth=max_depth) for a in args))

            return value
        except RuntimeError:
            e_type, value, traceback = sys.exc_info()
            raise ClaripyRecursionError, ("Recursion limit reached during display. I sorry.", e_type, value), traceback

    #
    # This code handles burrowing ITEs deeper into the ast and excavating
    # them to shallower levels.
    #

    def _deduplicate(self):
        return _deduplicate(self)

    def _simplify(self):
        return simplifier.simplify(self)


_hash_cache = weakref.WeakValueDictionary()
def _deduplicate(expr):
    return _hash_cache.setdefault(hash(expr), expr)

def _do_op(op, args):
    return get_structure(op, args)

def get_structure(op, args, annotations=()):
    return _deduplicate(ASTStructure(op, args, annotations=annotations))

from .. import operations
from ..errors import ClaripyRecursionError, ClaripyOperationError
from ..backend_manager import backends
from ..simplifier import simplifier
