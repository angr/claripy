import itertools
import logging
import weakref
import struct
import sys
import ana
from collections import Counter, defaultdict, deque

#import xxhash
#_hasher = xxhash.xxh64
#_hash_unpacker = struct.Struct('Q')
import hashlib
_hasher = hashlib.md5
_hash_unpacker = struct.Struct('2Q')
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
        self._canonical_info = None

    def __hash__(self):
        return _hash_unpacker.unpack(self._get_hash())[0] # 64 bits

    def _get_hash(self):
        """
        Calculates the hash of an ASTStructure.
        """
        if self._hash is None:
            args_tup = tuple(
                long(a) if type(a) is int else
                a if type(a) in (long, float) else
                a._get_hash() if type(a) is ASTStructure else
                hash(a)
                for a in self.args
            )
            to_hash = (self.op, args_tup, hash(self.annotations))

            # Why do we use md5 when it's broken? Because speed is more important
            # than cryptographic integrity here. Then again, look at all those
            # allocations we're doing here... fast python is painful.
            self._hash = _hasher(str(to_hash)).digest()
        return self._hash

    def __eq__(self, o):
        # special-case for BVV and BoolV
        if type(o) in (int, long, float, bool):
            if self.op in operations.backend_creation_operations:
                return self.args[0] == o
            else:
                return False

        if type(o) is not ASTStructure:
            return False

        return self is o or self._get_hash() == o._get_hash() # or (self.op == o.op and self.args == o.args and self.annotations == o.annotations)
    def __ne__(self, o):
        return not self.__eq__(o)

    def _compare_args(self, other_args):
        if isinstance(self.args, tuple):
            return all(a is b for a, b in zip(self.args, other_args))
        else:
            return False

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

    def swap_args(self, args, op=None):
        op = op if op else self.op
        if self._compare_args(args) and op == self.op:
            return self
        return get_structure(op, args, self.annotations)

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

            if not self._compare_args(new_args):
                r = _deduplicate(self.swap_args(tuple(new_args)))
            else:
                r = self

        replacements[self] = r
        return r

    def canonicalize(self):
        """
        Converts the structure to a canonical form:
            * Correct any "backwards" ops (`radd` -> `add`, `lt` -> `gt`)
            * Use the structure of the operations to generate a "hash" of
                  each variable independent of the name
            * Normalize variable names (ordering *should* be consistent)
            * Sort args of commutative operations

        TODO: Add support for variable length bitvectors

        :returns: a tuple of (variable_mapping, canonicalized_structure)
        """

        if self._canonical_info is not None:
            return self._canonical_info

        working_ast = self


        # Swap reversed ops (`radd` -> `add`, `lt` -> `gt`)

        replacements = { }
        for v in working_ast._bottom_up_dfs():
            if v.op in operations.nonstandard_reversible_ops and len(v.args) == 2:
                replacements[v] = v.swap_args(v.args[::-1],
                                              op=operations.nonstandard_reversible_ops[v.op])

        working_ast = working_ast.replace(replacements)


        # Generate variable (BVS, BoolS, and FPS) hashes

        variable_map = defaultdict(Counter)

        def _traverse(node_stack):
            current_node = node_stack[-1][1]
            if current_node.op in operations.backend_creation_operations or \
               current_node.op in operations.backend_symbol_creation_operations:
                # the DRESEL COMMUTATION INDEPENDENT PATH OPERATION TRACE (TM)
                path_trace = tuple((v.op, i) for i, v in node_stack)
                path_trace += (current_node.args[1:],)
                variable_map[current_node][path_trace] += 1
                return

            for index, node in enumerate(current_node.args):
                if isinstance(node, ASTStructure):
                    node_stack.append((None if current_node.op in operations.commutative_operations else index,
                                       node))
                    _traverse(node_stack)
                    node_stack.pop()

        stack = [(0, working_ast)]
        _traverse(stack)

        sorted_map = { node: tuple(sorted(c.iteritems(), key=lambda x: hash(x[0]))) for node, c in variable_map.iteritems() }
        hash_map = { node: hash(v) for node, v in sorted_map.iteritems() }
        sorted_nodes = tuple(sorted(hash_map.iterkeys(), key=lambda x: hash_map[x]))

        full_hash_map = hash_map.copy()
        it = list(working_ast._bottom_up_dfs())
        for node in it:
            if node not in full_hash_map:
                if node.op in operations.commutative_operations:
                    args = tuple(sorted(node.args, key=lambda x: full_hash_map[x]))
                else:
                    args = node.args

                full_hash_map[node] = hash(tuple(map(lambda x: full_hash_map[x], args)))

        q = []
        q.append(working_ast)
        name_mapping = { }
        while len(q) > 0:
            node = q.pop()
            q.extend(sorted(filter(lambda arg: isinstance(arg, ASTStructure), node.args),
                            key=lambda x: full_hash_map[x]))
            if node.op in operations.backend_symbol_creation_operations and node not in name_mapping:
                name_mapping[node] = "cv%d" % len(name_mapping)

        # Rename the variables

        replacements = { node: node.swap_args((name_mapping[node],) + node.args[1:]) for node in sorted_nodes if node.op in operations.backend_symbol_creation_operations }

        working_ast = working_ast.replace(replacements)


        # Sort commutative operations

        """
        replacements = { }
        for v in working_ast._bottom_up_dfs():
            if v.op in operations.commutative_operations:
                replacements[v] = v.swap_args(tuple(sorted(v.args, key=lambda x: hash(x))))

        working_ast = working_ast.replace(replacements)
        """

        early_leaves = set()
        while True:
            for v in working_ast._bottom_up_bfs(preleaves=early_leaves):
                early_leaves.add(v)
                if v.op in operations.commutative_operations:
                    new_args = tuple(sorted(v.args, key=lambda x: hash(x)))
                    if not v._compare_args(new_args):
                        working_ast = working_ast.replace({v: v.swap_args(new_args)})
                        break
            else:
                break

        self._canonical_info = (name_mapping, working_ast)
        return self._canonical_info

    def __contains__(self, other):
        """
        Checks if `other` is a subtree of `self`.
        """

        """
        TODO: make this more efficient . . .
            - get height of other, only iterate over nodes in self that are at
                that level?
        """

        for v in self._bottom_up_dfs():
            if v == other:
                return True

        return False

    def canonically_contains(self, other):
        """
        Checks if the cannonical version of `other` is a subtree of the
        canonical version of `self`.

        :param other: The ASTStructure to check for inside self

        :returns: True if other is in self, False otherwise
        """

        """
        TODO: make this more efficient . . .
            - get height of other, only iterate over nodes in self that are at
                that level?
        """

        canonical_other_stuff = other.canonicalize()
        canonical_other = canonical_other_stuff[1]

        for v in self._bottom_up_dfs():
            if v.canonicalize()[1] == canonical_other:
                return True

        return False

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
            u = str(self._get_hash()) if uuid is None else uuid
            ana.get_dl().uuid_cache[u] = self
            setattr(self, '_ana_uuid', u)
        return u

    def _bottom_up_dfs(self):
        for a in self.args:
            if isinstance(a, ASTStructure):
                for b in a._bottom_up_dfs():
                    yield b
        yield self

    def _bfs(self, preleaves=()):
        q = deque()
        q.appendleft(self)
        while len(q) > 0:
            node = q.pop()
            q.extendleft(filter(lambda x: isinstance(x, ASTStructure) and x not in preleaves, node.args))
            yield node

    def _bottom_up_bfs(self, preleaves=()):
        stack = list(self._bfs(preleaves=preleaves))
        while len(stack) > 0:
            yield stack.pop()


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
                args = tuple(self.args[::-1])
            else:
                op = self.op
                args = tuple(self.args)

            if op == 'BVS' and inner:
                value = args[0]
            elif op == 'BVS':
                value = "%s" % args[0]
                extras = [ ]
                # from ast.bv.BVS(): n, length, min, max, stride, uninitialized, discrete_set, discrete_set_max_card

                if args[2] is not None:
                    extras.append("min=%s" % args[2])
                if args[3] is not None:
                    extras.append("max=%s" % args[3])
                if args[4] is not None:
                    extras.append("stride=%s" % args[4])
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

#
# Deduplication helpers
#

_hash_cache = weakref.WeakValueDictionary()
def _deduplicate(expr):
    return _hash_cache.setdefault(expr._get_hash(), expr)

def _do_op(op, args):
    return get_structure(op, args)

def get_structure(op, args, annotations=()):
    return _deduplicate(ASTStructure(op, args, annotations=annotations))

#
# These are structures for true and false boolean ASTs
#

_true_structure = get_structure('BoolV', (True,))
_false_structure = get_structure('BoolV', (False,))

from .. import operations
from ..errors import ClaripyRecursionError, ClaripyOperationError
from ..backend_manager import backends
from ..simplifier import simplifier
