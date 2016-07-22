import os
import sys
import struct
import weakref
import hashlib
import itertools
import collections
import cPickle as pickle

import logging
l = logging.getLogger("claripy.ast")

import ana

WORKER = bool(os.environ.get('WORKER', False))
md5_unpacker = struct.Struct('2Q')

#pylint:enable=unused-argument
#pylint:disable=unidiomatic-typecheck

def _inner_repr(a, **kwargs):
    if isinstance(a, Base):
        return a.__repr__(inner=True, **kwargs)
    else:
        return repr(a)

class ASTCacheKey(object):
    def __init__(self, a):
        self.ast = a

    def __hash__(self):
        return hash(self.ast)

    def __eq__(self, other):
        return hash(self.ast) == hash(other.ast)

    def __repr__(self):
        return '<Key %s %s>' % (self.ast._type_name(), self.ast.__repr__(inner=True))

#
# AST variable naming
#

var_counter = itertools.count()
_unique_names = True

def _make_name(name, size, explicit_name=False, prefix=""):
    if _unique_names and not explicit_name:
        return "%s%s_%d_%d" % (prefix, name, var_counter.next(), size)
    else:
        return name


class Base(ana.Storable):
    """
    An AST tracks a tree of operations on arguments. It has the following methods:

        op: the operation that is being done on the arguments
        args: the arguments that are being used
        length: the length (in bits)

    AST objects have *hash identity*. This means that an AST that has the same hash as
    another AST will be the *same* object. For example, the following is true:

        a, b = two different ASTs
        c = b + a
        d = b + a
        assert c is d

    This is done to better support serialization and better manage memory.
    """

    __slots__ = [ 'op', 'args', 'variables', 'symbolic', '_hash', '_simplified',
                  '_cache_key', '_errored', '_eager_backends', 'length', '_excavated', '_burrowed', '_uninitialized',
                  '_uc_alloc_depth', 'annotations', 'simplifiable', '_uneliminatable_annotations', '_relocatable_annotations']
    _hash_cache = weakref.WeakValueDictionary()

    FULL_SIMPLIFY=1
    LITE_SIMPLIFY=2
    UNSIMPLIFIED=0

    def __new__(cls, op, args, **kwargs):
        """
        This is called when you create a new Base object, whether directly or through an operation.
        It finalizes the arguments (see the _finalize function, above) and then computes
        a hash. If an AST of this hash already exists, it returns that AST. Otherwise,
        it creates, initializes, and returns the AST.

        :param op:              The AST operation ('__add__', 'Or', etc)
        :param args:            The arguments to the AST operation (i.e., the objects to add)
        :param variables:       The symbolic variables present in the AST (default: empty set)
        :param symbolic:        A flag saying whether or not the AST is symbolic (default: False)
        :param length:          An integer specifying the length of this AST (default: None)
        :param collapsible:     A flag of whether or not Claripy can feel free to collapse this AST. This is mostly used
                                to keep Claripy from collapsing Reverse operations, so that they can be undone with
                                another Reverse.
        :param simplified:      A measure of how simplified this AST is. 0 means unsimplified, 1 means fast-simplified
                                (basically, just undoing the Reverse op), and 2 means simplified through z3.
        :param errored:         A set of backends that are known to be unable to handle this AST.
        :param eager_backends:  A list of backends with which to attempt eager evaluation
        :param annotations:     A frozenset of annotations applied onto this AST.
        """

        #if any(isinstance(a, BackendObject) for a in args):
        #   raise Exception('asdf')

        # fix up args and kwargs
        a_args = tuple((a.to_claripy() if isinstance(a, BackendObject) else a) for a in args)
        if 'symbolic' not in kwargs:
            kwargs['symbolic'] = any(a.symbolic for a in a_args if isinstance(a, Base))
        if 'variables' not in kwargs:
            kwargs['variables'] = frozenset.union(
                frozenset(), *(a.variables for a in a_args if isinstance(a, Base))
            )
        elif type(kwargs['variables']) is not frozenset: #pylint:disable=unidiomatic-typecheck
            kwargs['variables'] = frozenset(kwargs['variables'])
        if 'errored' not in kwargs:
            kwargs['errored'] = set.union(set(), *(a._errored for a in a_args if isinstance(a, Base)))

        if 'add_variables' in kwargs:
            kwargs['variables'] = kwargs['variables'] | kwargs['add_variables']

        eager_backends = list(backends._eager_backends) if 'eager_backends' not in kwargs else kwargs['eager_backends']

        if not kwargs['symbolic'] and eager_backends is not None and op not in operations.leaf_operations:
            for eb in eager_backends:
                try:
                    r = operations._handle_annotations(eb._abstract(eb.call(op, args)), args)
                    if r is not None:
                        return r
                    else:
                        eager_backends.remove(eb)
                except BackendError:
                    eager_backends.remove(eb)

        # if we can't be eager anymore, null out the eagerness
        kwargs['eager_backends'] = None

        # whether this guy is initialized or not
        if 'uninitialized' not in kwargs:
            kwargs['uninitialized'] = None

        if 'uc_alloc_depth' not in kwargs:
            kwargs['uc_alloc_depth'] = None

        if 'annotations' not in kwargs:
            kwargs['annotations'] = ()

        h = Base._calc_hash(op, a_args, kwargs)
        self = cls._hash_cache.get(h, None)
        if self is None:
            self = super(Base, cls).__new__(cls, op, a_args, **kwargs)
            self.__a_init__(op, a_args, **kwargs)
            self._hash = h
            cls._hash_cache[h] = self
        # else:
        #    if self.args != f_args or self.op != f_op or self.variables != f_kwargs['variables']:
        #        raise Exception("CRAP -- hash collision")

        return self

    def __init__(self, *args, **kwargs):
        pass

    @staticmethod
    def _calc_hash(op, args, k):
        """
        Calculates the hash of an AST, given the operation, args, and kwargs.

        :param op:      The operation.
        :param args:    The arguments to the operation.
        :param kwargs:  A dict including the 'symbolic', 'variables', and 'length' items.

        :returns:       a hash.

        """
        args_tup = tuple(long(a) if type(a) is int else (a if type(a) in (long, float) else hash(a)) for a in args)
        to_hash = (op, args_tup, k['symbolic'], hash(k['variables']), str(k.get('length', None)), hash(k.get('annotations', None)))

        # Why do we use md5 when it's broken? Because speed is more important
        # than cryptographic integrity here. Then again, look at all those
        # allocations we're doing here... fast python is painful.
        hd = hashlib.md5(pickle.dumps(to_hash, -1)).digest()
        return md5_unpacker.unpack(hd)[0] # 64 bits

    def _get_hashables(self):
        return self.op, tuple(str(a) if type(a) in (int, long, float) else hash(a) for a in self.args), self.symbolic, hash(self.variables), str(self.length)

    #pylint:disable=attribute-defined-outside-init
    def __a_init__(self, op, args, variables=None, symbolic=None, length=None, collapsible=None, simplified=0, errored=None, eager_backends=None, add_variables=None, uninitialized=None, uc_alloc_depth=None, annotations=None): #pylint:disable=unused-argument
        """
        Initializes an AST. Takes the same arguments as Base.__new__()
        """
        self.op = op
        self.args = args
        self.length = length
        self.variables = frozenset(variables)
        self.symbolic = symbolic
        self._eager_backends = eager_backends

        self._errored = errored if errored is not None else set()

        self._simplified = simplified
        self._cache_key = ASTCacheKey(self)
        self._excavated = None
        self._burrowed = None

        self._uninitialized = uninitialized
        self._uc_alloc_depth = uc_alloc_depth
        self.annotations = annotations

        ast_args = tuple(a for a in self.args if isinstance(a, Base))
        self._uneliminatable_annotations = frozenset(itertools.chain(
            itertools.chain.from_iterable(a._uneliminatable_annotations for a in ast_args),
            tuple(a for a in self.annotations if not a.eliminatable and not a.relocatable)
        ))

        self._relocatable_annotations = collections.OrderedDict((e, True) for e in tuple(itertools.chain(
            itertools.chain.from_iterable(a._relocatable_annotations for a in ast_args),
            tuple(a for a in self.annotations if not a.eliminatable and a.relocatable)
        ))).keys()

        if len(args) == 0:
            raise ClaripyOperationError("AST with no arguments!")

        #if self.op != 'I':
        #    for a in args:
        #        if not isinstance(a, Base) and type(a) not in (int, long, bool, str, unicode):
        #            import ipdb; ipdb.set_trace()
        #            l.warning(ClaripyOperationError("Un-wrapped native object of type %s!" % type(a)))
    #pylint:enable=attribute-defined-outside-init

    def make_uuid(self, uuid=None):
        """
        This overrides the default ANA uuid with the hash of the AST. UUID is slow, and we'll soon replace it from ANA
        itself, and this will go away.

        :returns: a string representation of the AST hash.
        """
        u = getattr(self, '_ana_uuid', None)
        if u is None:
            u = str(self._hash) if uuid is None else uuid
            ana.get_dl().uuid_cache[u] = self
            setattr(self, '_ana_uuid', u)
        return u

    @property
    def uuid(self):
        return self.ana_uuid

    def __hash__(self):
        return self._hash

    @property
    def cache_key(self):
        return self._cache_key

    #
    # Serialization support
    #

    def _ana_getstate(self):
        """
        Support for ANA serialization.
        """
        return self.op, self.args, self.length, self.variables, self.symbolic, self._hash, self.annotations

    def _ana_setstate(self, state):
        """
        Support for ANA deserialization.
        """
        op, args, length, variables, symbolic, h, annotations = state
        Base.__a_init__(self, op, args, length=length, variables=variables, symbolic=symbolic, annotations=annotations)
        self._hash = h
        Base._hash_cache[h] = self

    #
    # Collapsing and simplification
    #

    #def _models_for(self, backend):
    #    for a in self.args:
    #        backend.convert_expr(a)
    #        else:
    #            yield backend.convert(a)

    def make_like(self, *args, **kwargs):
        all_operations = operations.leaf_operations_symbolic | {'union'}
        if 'annotations' not in kwargs: kwargs['annotations'] = self.annotations
        if 'variables' not in kwargs and self.op in all_operations: kwargs['variables'] = self.variables
        if 'uninitialized' not in kwargs: kwargs['uninitialized'] = self._uninitialized
        if 'symbolic' not in kwargs and self.op in all_operations: kwargs['symbolic'] = self.symbolic
        return type(self)(*args, **kwargs)

    def _rename(self, new_name):
        if self.op not in { 'BVS', 'BoolS', 'FPS' }:
            raise ClaripyOperationError("rename is only supported on leaf nodes")
        new_args = (new_name,) + self.args[1:]
        return self.make_like(self.op, new_args, length=self.length, variables={new_name})

    #
    # Annotations
    #

    def _apply_to_annotations(self, f):
        return self.make_like(self.op, self.args, annotations=f(self.annotations))

    def append_annotation(self, a):
        """
        Appends an annotation to this AST.

        :param a: the annotation to append
        :returns: a new AST, with the annotation added
        """
        return self._apply_to_annotations(lambda alist: alist + (a,))

    def append_annotations(self, new_tuple):
        """
        Appends several annotations to this AST.

        :param new_tuple: the tuple of annotations to append
        :returns: a new AST, with the annotations added
        """
        return self._apply_to_annotations(lambda alist: alist + new_tuple)

    def annotate(self, *args):
        """
        Appends annotations to this AST.

        :param *args: the tuple of annotations to append
        :returns: a new AST, with the annotations added
        """
        return self._apply_to_annotations(lambda alist: alist + args)

    def insert_annotation(self, a):
        """
        Inserts an annotation to this AST.

        :param a: the annotation to insert
        :returns: a new AST, with the annotation added
        """
        return self._apply_to_annotations(lambda alist: (a,) + alist)

    def insert_annotations(self, new_tuple):
        """
        Inserts several annotations to this AST.

        :param new_tuple: the tuple of annotations to insert
        :returns: a new AST, with the annotations added
        """
        return self._apply_to_annotations(lambda alist: new_tuple + alist)

    def replace_annotations(self, new_tuple):
        """
        Replaces annotations on this AST.

        :param new_tuple: the tuple of annotations to replace the old annotations with
        :returns: a new AST, with the annotations added
        """
        return self._apply_to_annotations(lambda alist: new_tuple)

    def remove_annotation(self, a):
        """
        Removes an annotation from this AST.

        :param a: the annotation to remove
        :returns: a new AST, with the annotation removed
        """
        return self._apply_to_annotations(lambda alist: tuple(oa for oa in alist if oa != a))

    def remove_annotations(self, remove_sequence):
        """
        Removes several annotations from this AST.

        :param remove_sequence: a sequence/set of the annotations to remove
        :returns: a new AST, with the annotations removed
        """
        return self._apply_to_annotations(lambda alist: tuple(oa for oa in alist if oa not in remove_sequence))

    #
    # Viewing and debugging
    #

    def dbg_repr(self, prefix=None):
        try:
            if prefix is not None:
                new_prefix = prefix + "    "
                s = prefix + "<%s %s (\n" % (type(self).__name__, self.op)
                for a in self.args:
                    s += "%s,\n" % (a.dbg_repr(prefix=new_prefix) if hasattr(a, 'dbg_repr') else (new_prefix + repr(a)))
                s = s[:-2] + '\n'
                s += prefix + ")>"

                return s
            else:
                return "<%s %s (%s)>" % (type(self).__name__, self.op, ', '.join(a.dbg_repr() if hasattr(a, 'dbg_repr') else repr(a) for a in self.args))
        except RuntimeError:
            e_type, value, traceback = sys.exc_info()
            raise ClaripyRecursionError, ("Recursion limit reached during display. I sorry.", e_type, value), traceback

    def _type_name(self):
        return self.__class__.__name__

    def shallow_repr(self, max_depth=8):
        return self.__repr__(max_depth=max_depth)

    def __repr__(self, inner=False, max_depth=None, explicit_length=False):
        if max_depth is not None and max_depth <= 0:
            return '<...>'

        if max_depth is not None:
            max_depth -= 1

        if WORKER:
            return '<AST something>'

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
                if args[1] is not None:
                    extras.append("min=%s" % args[1])
                if args[2] is not None:
                    extras.append("max=%s" % args[2])
                if args[3] is not None:
                    extras.append("stride=%s" % args[3])
                if args[4] is True:
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
                value += ('#' + str(self.length)) if explicit_length else ''
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

            if not inner:
                value = '<{} {}>'.format(self._type_name(), value)

            return value
        except RuntimeError:
            e_type, value, traceback = sys.exc_info()
            raise ClaripyRecursionError, ("Recursion limit reached during display. I sorry.", e_type, value), traceback

    @property
    def depth(self):
        """
        The depth of this AST. For example, an AST representing (a+(b+c)) would have a depth of 2.
        """
        return self._depth()

    def _depth(self, memoized=None):
        """
        :param memoized:    A dict of ast hashes to depths we've seen before
        :return:            The depth of the AST. For example, an AST representing (a+(b+c)) would have a depth of 2.
        """
        if memoized is None:
            memoized = dict()

        ast_args = [ a for a in self.args if isinstance(a, Base) ]
        max_depth = 0
        for a in ast_args:
            if a.cache_key not in memoized:
                memoized[a.cache_key] = a._depth(memoized)
            max_depth = max(memoized[a.cache_key], max_depth)

        return 1 + max_depth

    @property
    def recursive_children_asts(self):
        for a in self.args:
            if isinstance(a, Base):
                l.debug("Yielding AST %s with hash %s with %d children", a, hash(a), len(a.args))
                yield a
                for b in a.recursive_children_asts:
                    yield b

    @property
    def recursive_leaf_asts(self):
        return self._recursive_leaf_asts()

    def _recursive_leaf_asts(self, seen=None):
        if self.depth == 1:
            yield self
            return

        seen = set() if seen is None else seen
        for a in self.args:
            if isinstance(a, Base) and not a.cache_key in seen:
                seen.add(a.cache_key)

                if a.depth == 1:
                    yield a
                else:
                    for b in a.recursive_leaf_asts:
                        yield b

    def dbg_is_looped(self, seen=None, checked=None):
        seen = set() if seen is None else seen
        checked = set() if checked is None else checked

        l.debug("Checking AST with hash %s for looping", hash(self))
        if hash(self) in seen:
            return self
        elif hash(self) in checked:
            return False
        else:
            seen.add(hash(self))

            for a in self.args:
                if not isinstance(a, Base):
                    continue

                r = a.dbg_is_looped(seen=set(seen), checked=checked)
                if r is not False:
                    return r

            checked.add(hash(self))
            return False

    #
    # Various AST modifications (replacements)
    #

    def _replace(self, replacements, variable_set=None, leaf_operation=None):
        """
        A helper for replace().

        :param variable_set: For optimization, ast's without these variables are not checked for replacing.
        :param replacements: A dictionary of hashes to their replacements.
        """
        try:
            if variable_set is None:
                variable_set = set()

            hash_key = self.cache_key

            if hash_key in replacements:
                r = replacements[hash_key]
            elif not self.variables.issuperset(variable_set):
                r = self
            elif leaf_operation is not None and self.op in operations.leaf_operations:
                r = leaf_operation(self)
                if r is not self:
                    replacements[hash_key] = r
                return r
            else:
                new_args = [ ]
                replaced = False

                for a in self.args:
                    if isinstance(a, Base):
                        new_a = a._replace(replacements=replacements, variable_set=variable_set, leaf_operation=leaf_operation)
                        replaced |= new_a is not a
                    else:
                        new_a = a

                    new_args.append(new_a)

                if replaced:
                    r = self.make_like(self.op, tuple(new_args))
                    replacements[hash_key] = r
                else:
                    r = self

            return r
        except ClaripyReplacementError:
            l.error("Replacement error:", exc_info=True)
            return self

    def swap_args(self, new_args, new_length=None):
        """
        This returns the same AST, with the arguments swapped out for new_args.
        """

        if len(self.args) == len(new_args) and all(a is b for a,b in zip(self.args, new_args)):
            return self

        #symbolic = any(a.symbolic for a in new_args if isinstance(a, Base))
        #variables = frozenset.union(frozenset(), *(a.variables for a in new_args if isinstance(a, Base)))
        length = self.length if new_length is None else new_length
        a = self.__class__(self.op, new_args, length=length)
        #if a.op != self.op or a.symbolic != self.symbolic or a.variables != self.variables:
        #   raise ClaripyOperationError("major bug in swap_args()")
        return a

    #
    # Other helper functions
    #

    def split(self, split_on):
        """
        Splits the AST if its operation is `split_on` (i.e., return all the arguments). Otherwise, return a list with
        just the AST.
        """
        if self.op in split_on: return list(self.args)
        else: return [ self ]

    # we don't support iterating over Base objects
    def __iter__(self):
        """
        This prevents people from iterating over ASTs.
        """
        raise ClaripyOperationError("Please don't iterate over, or split, AST nodes!")

    def __nonzero__(self):
        """
        This prevents people from accidentally using an AST as a condition. For
        example, the following was previously common::

            a,b = two ASTs
            if a == b:
                do something

        The problem is that `a == b` would return an AST, because an AST can be symbolic
        and there could be no way to actually know the value of that without a
        constraint solve. This caused tons of issues.
        """
        raise ClaripyOperationError('testing Expressions for truthiness does not do what you want, as these expressions can be symbolic')

    def structurally_match(self, o):
        """
        Structurally compares two A objects, and check if their corresponding leaves are definitely the same A object
        (name-wise or hash-identity wise).

        :param o: the other claripy A object
        :return: True/False
        """

        # TODO: Convert a and b into canonical forms

        if self.op != o.op:
            return False

        if len(self.args) != len(o.args):
            return False

        for arg_a, arg_b in zip(self.args, o.args):
            if not isinstance(arg_a, Base):
                if type(arg_a) != type(arg_b):
                    return False
                # They are not ASTs
                if arg_a != arg_b:
                    return False
                else:
                    continue

            if arg_a.op in ('I', 'BVS', 'FP'):
                # This is a leaf node in AST tree
                if arg_a is not arg_b:
                    return False

            else:
                if not arg_a.structurally_match(arg_b):
                    return False

        return True

    def replace(self, old, new):
        """
        Returns an AST with all instances of the AST 'old' replaced with AST 'new'.
        """
        self._check_replaceability(old, new)
        replacements = {old.cache_key: new}
        return self._replace(replacements, variable_set=old.variables)

    def replace_dict(self, replacements):
        """
        :param replacements:    A dictionary of asts to replace and their replacements.
        :return:                An AST with all instances of ast's in replacements.
        """
        #for old, new in replacements.items():
        #   old = old.ast
        #   if not isinstance(old, Base) or not isinstance(new, Base):
        #       raise ClaripyOperationError('replacements must be AST nodes')
        #   if type(old) is not type(new):
        #       raise ClaripyOperationError('cannot replace type %s ast with type %s ast' % (type(old), type(new)))
        #   old._check_replaceability(new)

        return self._replace(replacements, variable_set=set())

    @staticmethod
    def _check_replaceability(old, new):
        if not isinstance(old, Base) or not isinstance(new, Base):
            raise ClaripyReplacementError('replacements must be AST nodes')
        if type(old) is not type(new):
            raise ClaripyReplacementError('cannot replace type %s ast with type %s ast' % (type(old), type(new)))

    def _identify_vars(self, all_vars, counter):
        if self.op == 'BVS':
            if self.args not in all_vars:
                all_vars[self.args] = BV('BVS', self.args, length=self.length, explicit_name=True)
        elif self.op == 'BoolS':
            if self.args not in all_vars:
                all_vars[self.args] = BoolS('var_' + str(next(counter)))
        else:
            for arg in self.args:
                if isinstance(arg, Base):
                    arg._identify_vars(all_vars, counter)

    def canonicalize(self, var_map=None, counter=None):
        counter = itertools.count() if counter is None else counter
        var_map = { } if var_map is None else var_map

        for v in self._recursive_leaf_asts():
            if v.cache_key not in var_map and v.op in { 'BVS', 'BoolS', 'FPs' }:
                new_name = 'canonical_%d' % next(counter)
                var_map[v.cache_key] = v._rename(new_name)

        return var_map, counter, self.replace_dict(var_map)

    #
    # This code handles burrowing ITEs deeper into the ast and excavating
    # them to shallower levels.
    #

    def _burrow_ite(self):
        if self.op != 'If':
            #print "i'm not an if"
            return self.swap_args([ (a.ite_burrowed if isinstance(a, Base) else a) for a in self.args ])

        if not all(isinstance(a, Base) for a in self.args):
            #print "not all my args are bases"
            return self

        old_true = self.args[1]
        old_false = self.args[2]

        if old_true.op != old_false.op or len(old_true.args) != len(old_false.args):
            return self

        if old_true.op == 'If':
            # let's no go into this right now
            return self

        if any(a.op in {'BVS', 'BVV', 'FPS', 'FPV', 'BoolS', 'BoolV'} for a in self.args):
            # burrowing through these is pretty funny
            return self

        matches = [ old_true.args[i] is old_false.args[i] for i in range(len(old_true.args)) ]
        if matches.count(True) != 1 or all(matches):
            # TODO: handle multiple differences for multi-arg ast nodes
            #print "wrong number of matches:",matches,old_true,old_false
            return self

        different_idx = matches.index(False)
        inner_if = If(self.args[0], old_true.args[different_idx], old_false.args[different_idx])
        new_args = list(old_true.args)
        new_args[different_idx] = inner_if.ite_burrowed
        #print "replaced the",different_idx,"arg:",new_args
        return old_true.__class__(old_true.op, new_args, length=self.length)

    def _excavate_ite(self):
        if self.op in { 'BVS', 'I', 'BVV' }:
            return self

        excavated_args = [ (a.ite_excavated if isinstance(a, Base) else a) for a in self.args ]
        ite_args = [ isinstance(a, Base) and a.op == 'If' for a in excavated_args ]

        if self.op == 'If':
            # if we are an If, call the If handler so that we can take advantage of its simplifiers
            return If(*excavated_args)
        elif ite_args.count(True) == 0:
            # if there are no ifs that came to the surface, there's nothing more to do
            return self.swap_args(excavated_args)
        else:
            # this gets called when we're *not* in an If, but there are Ifs in the args.
            # it pulls those Ifs out to the surface.
            cond = excavated_args[ite_args.index(True)].args[0]
            new_true_args = [ ]
            new_false_args = [ ]

            for a in excavated_args:
                #print "OC", cond.dbg_repr()
                #print "NC", Not(cond).dbg_repr()

                if not isinstance(a, Base) or a.op != 'If':
                    new_true_args.append(a)
                    new_false_args.append(a)
                elif a.args[0] is cond:
                    #print "AC", a.args[0].dbg_repr()
                    new_true_args.append(a.args[1])
                    new_false_args.append(a.args[2])
                elif a.args[0] is Not(cond):
                    #print "AN", a.args[0].dbg_repr()
                    new_true_args.append(a.args[2])
                    new_false_args.append(a.args[1])
                else:
                    #print "AB", a.args[0].dbg_repr()
                    # weird conditions -- giving up!
                    return self.swap_args(excavated_args)

            return If(cond, self.swap_args(new_true_args), self.swap_args(new_false_args))

    @property
    def ite_burrowed(self):
        """
        Returns an equivalent AST that "burrows" the ITE expressions as deep as possible into the ast, for simpler
        printing.
        """
        if self._burrowed is None:
            self._burrowed = self._burrow_ite() #pylint:disable=attribute-defined-outside-init
            self._burrowed._burrowed = self._burrowed
        return self._burrowed

    @property
    def ite_excavated(self):
        """
        Returns an equivalent AST that "excavates" the ITE expressions out as far as possible toward the root of the
        AST, for processing in static analyses.
        """
        if self._excavated is None:
            self._excavated = self._excavate_ite() #pylint:disable=attribute-defined-outside-init

            # we set the flag for the children so that we avoid re-excavating during
            # VSA backend evaluation (since the backend evaluation recursively works on
            # the excavated ASTs)
            self._excavated._excavated = self._excavated
        return self._excavated

    #
    # these are convenience operations
    #

    def _first_backend(self, what):
        for b in backends._all_backends:
            if b in self._errored:
                continue

            try: return getattr(b, what)(self)
            except BackendError: pass

    @property
    def singlevalued(self):
        return self._first_backend('singlevalued')

    @property
    def multivalued(self):
        return self._first_backend('multivalued')

    @property
    def cardinality(self):
        return self._first_backend('cardinality')

    @property
    def concrete(self):
        return backends.concrete.handles(self)

    @property
    def uninitialized(self):
        """
        Whether this AST comes from an uninitialized dereference or not. It's only used in under-constrained symbolic
        execution mode.

        :return: True/False/None (unspecified).
        """

        #TODO: It should definitely be moved to the proposed Annotation backend.

        return self._uninitialized

    @property
    def uc_alloc_depth(self):
        """
        The depth of allocation by lazy-initialization. It's only used in under-constrained symbolic execution mode.

        :return: An integer indicating the allocation depth, or None if it's not from lazy-initialization.
        """
        # TODO: It should definitely be moved to the proposed Annotation backend.

        return self._uc_alloc_depth

    #
    # Backwards compatibility crap
    #

    @property
    def model(self):
        l.critical("DEPRECATION WARNING: do not use AST.model. It is deprecated, no longer does what is expected, and "
                   "will soon be removed. If you *need* to access the model use AST._model_X where X is the backend "
                   "that you are interested in.")
        print("DEPRECATION WARNING: do not use AST.model. It is deprecated, no longer does what is expected, and will "
              "soon be removed. If you *need* to access the model use AST._model_X where X is the backend that you are "
              "interested in.")
        return self._model_concrete if self._model_concrete is not self else \
               self._model_vsa if self._model_vsa is not self else \
               self._model_z3 if self._model_z3 is not self else \
               self

    def __getattr__(self, a):
        if not a.startswith('_model_'):
            raise AttributeError(a)

        model_name = a[7:]
        if not hasattr(backends, model_name):
            raise AttributeError(a)

        try:
            return getattr(backends, model_name).convert(self)
        except BackendError:
            return self

def simplify(e):
    if isinstance(e, Base) and e.op == 'I':
        return e

    s = e._first_backend('simplify')
    if s is None:
        l.debug("Unable to simplify expression")
        return e
    else:
        # Copy some parameters (that should really go to the Annotation backend)
        s._uninitialized = e.uninitialized
        s._uc_alloc_depth = e._uc_alloc_depth

        s._simplified = Base.FULL_SIMPLIFY

        return s

from ..errors import BackendError, ClaripyOperationError, ClaripyRecursionError, ClaripyReplacementError
from .. import operations
from ..backend_object import BackendObject
from ..backend_manager import backends
from ..ast.bool import If, Not, BoolS
from ..ast.bv import BV
