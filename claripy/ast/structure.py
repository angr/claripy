import itertools
import logging
import weakref
import struct
import sys
import ana
from .base import Base
from collections import Counter, defaultdict, deque, OrderedDict
from ..operations import backend_potentially_uninitialized as potentially_uninit, \
                         nonstandard_reversible_ops as reversible, \
                         backend_symbol_creation_operations as symbol_creation, \
                         commutative_operations as commutative, \
                         backend_creation_operations as literal_creation

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
        self._uninitialized = None if not self.op in potentially_uninit else self.args[5]
        self._hash = None
        self._variable_paths = None
        self._canonical_hash = None
        self._canonical_info = None

    def __hash__(self):
        return _hash_unpacker.unpack(self._get_hash())[0]  # 64 bits

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

        return self is o or self._get_hash() == o._get_hash()

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

    @property
    def uninitialized(self):
        if self._uninitialized is not None:
            return self._uninitialized

        self._uninitialized = any(a.uninitialized is True for a in self.args
                                  if isinstance(a, ASTStructure))
        return self._uninitialized

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
            new_args = tuple(
                a.replace(replacements=replacements, leaf_operation=leaf_operation)
                if isinstance(a, ASTStructure) else a
                for a in self.args
            )

            r = self.swap_args(new_args)

        replacements[self] = r
        return r

    def canonical_hash(self):
        if self._canonical_hash is not None:
            return self._canonical_hash

        if self.op in symbol_creation:
            path = ((self.op, 0),)
            counter = Counter()
            counter[path] += 1
            self._variable_paths = OrderedDict()
            self._variable_paths[self] = counter
            can_hash = hash((self.op,) + tuple(long(hash(t)) for t in self.args[1:]))
        elif self.op in literal_creation:
            self._variable_paths = OrderedDict()
            can_hash = hash((self.op,) + tuple(long(hash(t)) for t in self.args))
        else:
            if self.op in reversible:
                new_op   = reversible[self.op]
                new_args = self.args[::-1]
            else:
                new_op   = self.op
                new_args = self.args

            canonical_args = list(t.canonical_hash() if isinstance(t, ASTStructure) else long(hash(t))
                                  for t in new_args)

            tmp_var_paths = OrderedDict()

            for index, arg in enumerate(new_args):
                if not isinstance(arg, ASTStructure):
                    continue
                for var in arg._variable_paths:
                    if var not in tmp_var_paths:
                        tmp_var_paths[var] = Counter()
                    i = None if new_op in commutative else index
                    tmp_var_paths[var].update({
                            ((new_op, i),) + path: count
                            for path, count in arg._variable_paths[var].iteritems()
                        })

            modified_args = zip(canonical_args, ([tmp_var_paths[var]
                                                 for var in arg._variable_paths]
                                                 if isinstance(arg, ASTStructure) else None
                                                 for arg in new_args))
            sorted_args = sorted(zip(new_args, modified_args), key=lambda x: x[1])
            sorted_hashes = [a[1][0] for a in sorted_args]

            self._variable_paths = tmp_var_paths

            nameless = sorted([sorted(paths.iteritems()) for paths in self._variable_paths.itervalues()])

            can_hash = _hash_unpacker.unpack(_hasher(str(sorted_hashes) + str(nameless)).digest())[0]

        self._canonical_hash = long(can_hash)
        return self._canonical_hash

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

        l.warning("ASTStructure.canonicalize() is *very* slow. " +
                  "Consider using ASTStructure.canonical_hash() instead.")

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

                full_hash_map[node] = hash(tuple(full_hash_map[x] if isinstance(x, ASTStructure) else hash(x)
                                                 for x in args))

        q = [working_ast]
        name_mapping = {}
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

        pure_mapping = { node.args[0]: v for node, v in name_mapping.iteritems() }
        self._canonical_info = (pure_mapping, working_ast)
        trivial_mapping = { v: v for v in pure_mapping.itervalues() }
        working_ast._canonical_info = (trivial_mapping, working_ast)

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

        if isinstance(other, ASTStructure):
            other_struct = other
        elif isinstance(other, Base):
            other_struct = other.structure
        else:
            raise TypeError("in <ASTStructure> requires ASTStructure or Base " +
                            "as left operand, not %s" % type(other))

        for v in self._bottom_up_dfs():
            if v == other_struct:
                return True

        return False

    def canonically_equals(self, other):
        return self.canonical_hash() == other.canonical_hash()

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

        if isinstance(other, ASTStructure):
            other_struct = other
        elif isinstance(other, Base):
            other_struct = other.structure
        else:
            raise TypeError("in <ASTStructure> requires ASTStructure or Base " +
                            "as left operand, not %s" % type(other))

        canonical_other = other_struct.canonical_hash()

        for v in self._bottom_up_dfs():
            if v.canonical_hash() == canonical_other:
                return True

        return False

    def canonically_replace(self, replacements, is_hashmap=False):
        """
        Traverses `self` and, where a node canonically equals a key in of
        `replacements`, replace that node with the corresponding node in
        `replacements`

        :param replacements: A dictionary of nodes to their replacements.
        :param is_hashmap: if True, treat replacements as a dict of hashes

        :returns: the new tree
        """

        if not is_hashmap:
            swaps = {get_canonical_hash(n): v for n, v in replacements.iteritems()}
        else:
            swaps = replacements
        replace_args = {}

        self.canonical_hash()

        for node in self._bfs():
            key = node.canonical_hash()
            if key in swaps:
                given = swaps[key]
                if isinstance(given, ASTStructure):
                    rep = given
                elif isinstance(given, bool):
                    rep = _true_structure if given else _false_structure
                else:
                    raise TypeError(type(given))
                replace_args[node] = rep

        return self.replace(replace_args)
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
                for b in a.dbg_recursive_children:
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
            if isinstance(a, ASTStructure) and a not in seen:
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
                extras = []
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


def canonical_structure(s):
    if isinstance(s, ASTStructure):
        return s.canonicalize()[1]
    elif isinstance(s, Base):
        return s.structure.canonicalize()[1]
    else:
        raise TypeError("Unknown type %s passed to `canonical_structure`" % str(type(s)))


def get_canonical_hash(s):
    return get_structure_form(s).canonical_hash()


def get_structure_form(s):
    if isinstance(s, ASTStructure):
        return s
    elif isinstance(s, Base):
        return s.structure
    else:
        raise TypeError("Unknown type %s passed to `get_structure_form`" % str(type(s)))

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
