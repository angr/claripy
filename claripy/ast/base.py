import hashlib
import itertools
import logging
import os
import struct
import weakref
from collections import OrderedDict, deque

try:
    import cPickle as pickle
except ImportError:
    import pickle

l = logging.getLogger("claripy.ast")

WORKER = bool(os.environ.get('WORKER', False))
md5_unpacker = struct.Struct('2Q')

#pylint:enable=unused-argument
#pylint:disable=unidiomatic-typecheck


class ASTCacheKey:
    def __init__(self, a):
        self.ast = a

    def __hash__(self):
        return hash(self.ast)

    def __eq__(self, other):
        return type(self) is type(other) and self.ast._hash == other.ast._hash

    def __repr__(self):
        return '<Key %s %s>' % (self.ast._type_name(), self.ast.__repr__(inner=True))

#
# AST variable naming
#

var_counter = itertools.count()
_unique_names = True

def _make_name(name, size, explicit_name=False, prefix=""):
    if _unique_names and not explicit_name:
        return "%s%s_%d_%d" % (prefix, name, next(var_counter), size)
    else:
        return name

def _d(h, cls, state):
    """
    This function is the deserializer for ASTs.
    It exists to work around the fact that pickle will (normally) call __new__() with no arguments during deserialization.
    For ASTs, this does not work.
    """
    op, args, length, variables, symbolic, annotations = state
    return cls.__new__(cls, op, args, length=length, variables=variables, symbolic=symbolic, annotations=annotations, hash=h)

class Base:
    """
    This is the base class of all claripy ASTs. An AST tracks a tree of operations on arguments.

    This class should not be instanciated directly - instead, use one of the constructor functions (BVS, BVV, FPS,
    FPV...) to construct a leaf node and then build more complicated expressions using operations.

    AST objects have *hash identity*. This means that an AST that has the same hash as another AST will be the *same*
    object. This is critical for efficient memory usage. As an example, the following is true::

        a, b = two different ASTs
        c = b + a
        d = b + a
        assert c is d

    :ivar op:                       The operation that is being done on the arguments
    :ivar args:                     The arguments that are being used
    """

    __slots__ = [ 'op', 'args', 'variables', 'symbolic', '_hash', '_simplified', '_cached_encoded_name',
                  '_cache_key', '_errored', '_eager_backends', 'length', '_excavated', '_burrowed', '_uninitialized',
                  '_uc_alloc_depth', 'annotations', 'simplifiable', '_uneliminatable_annotations', '_relocatable_annotations',
                  'depth', '__weakref__']
    _hash_cache = weakref.WeakValueDictionary()

    FULL_SIMPLIFY=1
    LITE_SIMPLIFY=2
    UNSIMPLIFIED=0

    LITE_REPR=0
    MID_REPR=1
    FULL_REPR=2

    def __new__(cls, op, args, add_variables=None, hash=None, **kwargs): #pylint:disable=redefined-builtin
        """
        This is called when you create a new Base object, whether directly or through an operation.
        It finalizes the arguments (see the _finalize function, above) and then computes
        a hash. If an AST of this hash already exists, it returns that AST. Otherwise,
        it creates, initializes, and returns the AST.

        :param op:                  The AST operation ('__add__', 'Or', etc)
        :param args:                The arguments to the AST operation (i.e., the objects to add)
        :param variables:           The symbolic variables present in the AST (default: empty set)
        :param symbolic:            A flag saying whether or not the AST is symbolic (default: False)
        :param length:              An integer specifying the length of this AST (default: None)
        :param simplified:          A measure of how simplified this AST is. 0 means unsimplified,
                                        1 means fast-simplified (basically, just undoing the Reverse
                                        op), and 2 means simplified through z3.
        :param errored:             A set of backends that are known to be unable to handle this AST.
        :param eager_backends:      A list of backends with which to attempt eager evaluation
        :param annotations:         A frozenset of annotations applied onto this AST.
        """

        #if any(isinstance(a, BackendObject) for a in args):
        #   raise Exception('asdf')

        a_args = args if type(args) is tuple else tuple(args)

        # initialize the following properties: symbolic, variables and errored
        need_symbolic = 'symbolic' not in kwargs
        need_variables = 'variables' not in kwargs
        need_errored = 'errored' not in kwargs
        args_have_annotations = None
        # Note that `args_have_annotations` may not be set if we don't need to set any of the above variables, in which
        # case it will stay as None, and will be passed to __a_init__() "as is". __a_init__() will properly handle it
        # there.
        arg_max_depth = 0
        if need_symbolic or need_variables or need_errored:
            symbolic_flag = False
            variables_set = set()
            errored_set = set()
            for a in a_args:
                if not isinstance(a, Base): continue
                if need_symbolic and not symbolic_flag: symbolic_flag |= a.symbolic
                if need_variables: variables_set |= a.variables
                if need_errored: errored_set |= a._errored
                if args_have_annotations is not True:
                    args_have_annotations = args_have_annotations or bool(a.annotations)
                if arg_max_depth < a.depth: arg_max_depth = a.depth

            if need_symbolic: kwargs['symbolic'] = symbolic_flag
            if need_variables: kwargs['variables'] = frozenset(variables_set)
            if need_errored: kwargs['errored'] = errored_set

        if type(kwargs['variables']) is not frozenset:  #pylint:disable=unidiomatic-typecheck
            kwargs['variables'] = frozenset(kwargs['variables'])

        if add_variables:
            kwargs['variables'] = kwargs['variables'] | add_variables

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

        if 'annotations' not in kwargs or kwargs['annotations'] is None:
            kwargs['annotations'] = ()

        h = Base._calc_hash(op, a_args, kwargs) if hash is None else hash
        self = cls._hash_cache.get(h, None)
        if self is None:
            self = super(Base, cls).__new__(cls)
            depth = arg_max_depth + 1
            self.__a_init__(op, a_args, depth=depth, args_have_annotations=args_have_annotations, **kwargs)
            self._hash = h
            cls._hash_cache[h] = self
        # else:
        #    if self.args != f_args or self.op != f_op or self.variables != f_kwargs['variables']:
        #        raise Exception("CRAP -- hash collision")

        return self

    def __reduce__(self):
        # HASHCONS: these attributes key the cache
        # BEFORE CHANGING THIS, SEE ALL OTHER INSTANCES OF "HASHCONS" IN THIS FILE
        return _d, (self._hash, self.__class__, (self.op, self.args, self.length, self.variables, self.symbolic, self.annotations))

    def __init__(self, *args, **kwargs):
        pass

    @staticmethod
    def _calc_hash(op, args, keywords):
        """
        Calculates the hash of an AST, given the operation, args, and kwargs.

        :param op:                  The operation.
        :param args:                The arguments to the operation.
        :param keywords:            A dict including the 'symbolic', 'variables', and 'length' items.
        :returns:                   a hash.

        We do it using md5 to avoid hash collisions.
        (hash(-1) == hash(-2), for example)
        """
        args_tup = tuple(a if type(a) in (int, float) else hash(a) for a in args)
        # HASHCONS: these attributes key the cache
        # BEFORE CHANGING THIS, SEE ALL OTHER INSTANCES OF "HASHCONS" IN THIS FILE
        to_hash = (
            op, args_tup,
            str(keywords.get('length', None)),
            hash(keywords['variables']),
            keywords['symbolic'],
            hash(keywords.get('annotations', None)),
        )

        # Why do we use md5 when it's broken? Because speed is more important
        # than cryptographic integrity here. Then again, look at all those
        # allocations we're doing here... fast python is painful.
        hd = hashlib.md5(pickle.dumps(to_hash, -1)).digest()
        return md5_unpacker.unpack(hd)[0] # 64 bits

    #pylint:disable=attribute-defined-outside-init
    def __a_init__(self, op, args, variables=None, symbolic=None, length=None, simplified=0, errored=None, eager_backends=None, uninitialized=None, uc_alloc_depth=None, annotations=None, encoded_name=None, depth=None, args_have_annotations=None):  #pylint:disable=unused-argument
        """
        Initializes an AST. Takes the same arguments as ``Base.__new__()``

        We use this instead of ``__init__`` due to python's undesirable behavior w.r.t. automatically calling it on
        return from ``__new__``.
        """

        # HASHCONS: these attributes key the cache
        # BEFORE CHANGING THIS, SEE ALL OTHER INSTANCES OF "HASHCONS" IN THIS FILE
        self.op = op
        self.args = args if type(args) is tuple else tuple(args)
        self.length = length
        self.variables = frozenset(variables) if type(variables) is not frozenset else variables
        self.symbolic = symbolic
        self.annotations = annotations


        self.depth = depth if depth is not None else 1

        self._eager_backends = eager_backends
        self._cached_encoded_name = encoded_name

        self._errored = errored if errored is not None else set()

        self._simplified = simplified
        self._cache_key = ASTCacheKey(self)
        self._excavated = None
        self._burrowed = None

        self._uninitialized = uninitialized
        self._uc_alloc_depth = uc_alloc_depth

        if not annotations and not args_have_annotations:
            self._uneliminatable_annotations = frozenset()
            self._relocatable_annotations = frozenset()
        else:
            ast_args = tuple(a for a in self.args if isinstance(a, Base))
            self._uneliminatable_annotations = frozenset(itertools.chain(
                itertools.chain.from_iterable(a._uneliminatable_annotations for a in ast_args),
                tuple(a for a in self.annotations if not a.eliminatable and not a.relocatable)
            ))

            self._relocatable_annotations = OrderedDict((e, True) for e in tuple(itertools.chain(
                itertools.chain.from_iterable(a._relocatable_annotations for a in ast_args),
                tuple(a for a in self.annotations if not a.eliminatable and a.relocatable)
            ))).keys()

        if len(self.args) == 0:
            raise ClaripyOperationError("AST with no arguments!")

    #pylint:enable=attribute-defined-outside-init

    def __hash__(self):
        return self._hash

    @property
    def cache_key(self):
        """
        A key that refers to this AST - this value is appropriate for usage as a key in dictionaries.
        """
        return self._cache_key

    @property
    def _encoded_name(self):
        if self._cached_encoded_name is None:
            self._cached_encoded_name = self.args[0].encode()  # pylint: disable=attribute-defined-outside-init
        return self._cached_encoded_name

    #
    # Collapsing and simplification
    #

    #def _models_for(self, backend):
    #    for a in self.args:
    #        backend.convert_expr(a)
    #        else:
    #            yield backend.convert(a)

    def make_like(self, op, args, **kwargs):
        if kwargs.pop("simplify", False) is True:
            # Try to simplify the expression again
            simplified = simplifications.simpleton.simplify(op, args)
        else:
            simplified = None
        if simplified is not None:
            op = simplified.op

        all_operations = operations.leaf_operations_symbolic | {'union'}
        if 'annotations' not in kwargs: kwargs['annotations'] = self.annotations
        if 'variables' not in kwargs and op in all_operations: kwargs['variables'] = self.variables
        if 'uninitialized' not in kwargs: kwargs['uninitialized'] = self._uninitialized
        if 'symbolic' not in kwargs and op in all_operations: kwargs['symbolic'] = self.symbolic
        if simplified is None:
            # Cannot simplify the expression anymore
            return type(self)(op, args, **kwargs)
        else:
            # The expression is simplified
            r = type(self)(op, simplified.args, **kwargs)
            return r

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

        :param a:                   the annotation to append
        :returns:                   a new AST, with the annotation added
        """
        return self._apply_to_annotations(lambda alist: alist + (a,))

    def append_annotations(self, new_tuple):
        """
        Appends several annotations to this AST.

        :param new_tuple:           the tuple of annotations to append
        :returns:                   a new AST, with the annotations added
        """
        return self._apply_to_annotations(lambda alist: alist + new_tuple)

    def annotate(self, *args):
        """
        Appends annotations to this AST.

        :param args:                the tuple of annotations to append (variadic positional args)
        :returns:                   a new AST, with the annotations added
        """
        return self._apply_to_annotations(lambda alist: alist + args)

    def insert_annotation(self, a):
        """
        Inserts an annotation to this AST.

        :param a:                   the annotation to insert
        :returns:                   a new AST, with the annotation added
        """
        return self._apply_to_annotations(lambda alist: (a,) + alist)

    def insert_annotations(self, new_tuple):
        """
        Inserts several annotations to this AST.

        :param new_tuple:           the tuple of annotations to insert
        :returns:                   a new AST, with the annotations added
        """
        return self._apply_to_annotations(lambda alist: new_tuple + alist)

    def replace_annotations(self, new_tuple):
        """
        Replaces annotations on this AST.

        :param new_tuple:           the tuple of annotations to replace the old annotations with
        :returns:                   a new AST, with the annotations added
        """
        return self._apply_to_annotations(lambda alist: new_tuple)

    def remove_annotation(self, a):
        """
        Removes an annotation from this AST.

        :param a:                   the annotation to remove
        :returns:                   a new AST, with the annotation removed
        """
        return self._apply_to_annotations(lambda alist: tuple(oa for oa in alist if oa != a))

    def remove_annotations(self, remove_sequence):
        """
        Removes several annotations from this AST.

        :param remove_sequence:     a sequence/set of the annotations to remove
        :returns:                   a new AST, with the annotations removed
        """
        return self._apply_to_annotations(lambda alist: tuple(oa for oa in alist if oa not in remove_sequence))

    #
    # Viewing and debugging
    #

    def dbg_repr(self, prefix=None):  # pylint:disable=unused-argument
        """
        Returns a debug representation of this AST.
        """
        return self.shallow_repr(max_depth=None, details=Base.FULL_REPR)

    def _type_name(self):
        return self.__class__.__name__

    def __repr__(self, inner=False, max_depth=None, explicit_length=False):
        if WORKER:
            return '<AST something>'
        else:
            return self.shallow_repr(max_depth=max_depth, explicit_length=explicit_length, inner=inner)

    def shallow_repr(self, max_depth=8, explicit_length=False, details=LITE_REPR, inner=False, parent_prec=15, left=True):
        """
        Returns a string representation of this AST, but with a maximum depth to
        prevent floods of text being printed.

        :param max_depth:           The maximum depth to print.
        :param explicit_length:     Print lengths of BVV arguments.
        :param details:             An integer value specifying how detailed the output should be:
                                        LITE_REPR - print short repr for both operations and BVs,
                                        MID_REPR  - print full repr for operations and short for BVs,
                                        FULL_REPR - print full repr of both operations and BVs.
        :param inner:               whether or not it is an inner AST
        :param parent_prec:         parent operation precedence level
        :param left:                whether or not it is a left AST
        :returns:                   A string representing the AST
        """
        if max_depth is not None and max_depth <= 0:
                return '<...>'

        elif self.op in operations.reversed_ops:
            op = operations.reversed_ops[self.op]
            args = reversed(self.args)
        else:
            op = self.op
            args = self.args

        next_max_depth = max_depth-1 if max_depth is not None else None
        length = self.length if explicit_length else None
        # if operation is not in op_precedence, assign the "least operation precedence"
        op_prec = operations.op_precedence[op] if op in operations.op_precedence else 15

        args = [arg.shallow_repr(next_max_depth, explicit_length, details, True, op_prec, idx == 0) \
                if isinstance(arg, Base) else arg for idx, arg in enumerate(args)]

        prec_diff = parent_prec - op_prec
        inner_infix_use_par = prec_diff < 0 or prec_diff == 0 and not left
        inner_repr = self._op_repr(op, args, inner, length, details, inner_infix_use_par)

        if not inner:
            return "<{} {}>".format(self._type_name(), inner_repr)
        else:
            return inner_repr

    @staticmethod
    def _op_repr(op, args, inner, length, details, inner_infix_use_par):
        if details < Base.FULL_REPR:
            if op == 'BVS':
                extras = []
                if args[1] is not None:
                    fmt = '%#x' if type(args[1]) is int else '%s'
                    extras.append("min=%s" % (fmt % args[1]))
                if args[2] is not None:
                    fmt = '%#x' if type(args[2]) is int else '%s'
                    extras.append("max=%s" % (fmt % args[2]))
                if args[3] is not None:
                    fmt = '%#x' if type(args[3]) is int else '%s'
                    extras.append("stride=%s" % (fmt % args[3]))
                if args[4] is True:
                    extras.append("UNINITIALIZED")
                return "{}{}".format(args[0], '{%s}' % ', '.join(extras) if extras else '')

            elif op == 'BoolV':
                return str(args[0])

            elif op == 'BVV':
                if args[0] is None:
                    value = '!'
                elif args[1] < 10:
                    value = format(args[0], '')
                else:
                    value = format(args[0], '#x')
                return value + '#%d' % length if length is not None else value

        if details < Base.MID_REPR:
            if op == 'If':
                value = 'if {} then {} else {}'.format(args[0], args[1], args[2])
                return '({})'.format(value) if inner else value

            elif op == 'Not':
                return '!{}'.format(args[0])

            elif op == 'Extract':
                return '{}[{}:{}]'.format(args[2], args[0], args[1])

            elif op == 'ZeroExt':
                value = '0#{} .. {}'.format(args[0], args[1])
                return '({})'.format(value) if inner else value

            elif op in operations.prefix:
                assert len(args) == 1
                value = '{}{}'.format(operations.prefix[op], args[0])
                return '({})'.format(value) if inner and inner_infix_use_par else value

            elif op in operations.infix:
                value = ' {} '.format(operations.infix[op]).join(args)
                return '({})'.format(value) if inner and inner_infix_use_par else value

        return '{}({})'.format(op, ', '.join(map(str, args)))

    def children_asts(self):
        """
        Return an iterator over the nested children ASTs.
        """
        ast_queue = deque([iter(self.args)])
        while ast_queue:

            try:
                ast = next(ast_queue[-1])
            except StopIteration:
                ast_queue.pop()
                continue

            if isinstance(ast, Base):
                ast_queue.append(iter(ast.args))

                l.debug("Yielding AST %s with hash %s with %d children", ast, hash(ast), len(ast.args))
                yield ast

    def leaf_asts(self):
        """
        Return an iterator over the leaf ASTs.
        """
        seen = set()

        ast_queue = deque([self])
        while ast_queue:

            ast = ast_queue.pop()
            if isinstance(ast, Base) and id(ast.cache_key) not in seen:
                seen.add(id(ast.cache_key))

                if ast.depth == 1:
                    yield ast
                    continue

                ast_queue.extend(ast.args)
                continue

    # TODO: Deprecate this property
    @property
    def recursive_children_asts(self):
        """
        DEPRECATED: Use children_asts() instead.
        """
        return self.children_asts()

    # TODO: Deprecate this property
    @property
    def recursive_leaf_asts(self):
        """
        DEPRECATED: Use leaf_asts() instead.
        """
        return self.leaf_asts()

    def dbg_is_looped(self):
        l.debug("Checking AST with hash %s for looping", hash(self))

        seen = set()
        for child_ast in self.children_asts():
            if hash(child_ast) in seen:
                return child_ast
            seen.add(hash(child_ast))

        return False

    #
    # Various AST modifications (replacements)
    #

    def swap_args(self, new_args, new_length=None, **kwargs):
        """
        This returns the same AST, with the arguments swapped out for new_args.
        """

        if len(self.args) == len(new_args) and all(a is b for a,b in zip(self.args, new_args)):
            return self

        #symbolic = any(a.symbolic for a in new_args if isinstance(a, Base))
        #variables = frozenset.union(frozenset(), *(a.variables for a in new_args if isinstance(a, Base)))
        length = self.length if new_length is None else new_length
        a = self.make_like(self.op, new_args, length=length, **kwargs)
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

    def __bool__(self):
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

        :param o:                   the other claripy A object
        :returns:                   True/False
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

            if arg_a.op in operations.leaf_operations:
                if arg_a is not arg_b:
                    return False

            else:
                if not arg_a.structurally_match(arg_b):
                    return False

        return True

    def replace_dict(self, replacements, variable_set=None, leaf_operation=None):
        """
        Returns this AST with subexpressions replaced by those that can be found in `replacements`
        dict.

        :param variable_set:        For optimization, ast's without these variables are not checked
                                        for replacing.
        :param replacements:        A dictionary of hashes to their replacements.
        :param leaf_operation:      An operation that should be applied to the leaf nodes.
        :returns:                   An AST with all instances of ast's in replacements.
        """
        if variable_set is None:
            variable_set = set()

        if leaf_operation is None:
            leaf_operation = lambda x: x

        arg_queue = [iter([self])]
        rep_queue = []
        ast_queue = []

        while arg_queue:
            try:
                ast = next(arg_queue[-1])
                repl = ast

                if not isinstance(ast, Base):
                    rep_queue.append(repl)
                    continue

                elif ast.cache_key in replacements:
                    repl = replacements[ast.cache_key]

                elif ast.variables >= variable_set:

                    if ast.op in operations.leaf_operations:
                        repl = leaf_operation(ast)
                        if repl is not ast:
                            replacements[ast.cache_key] = repl

                    elif ast.depth > 1:
                        arg_queue.append(iter(ast.args))
                        ast_queue.append(ast)
                        continue

                rep_queue.append(repl)
                continue

            except StopIteration:
                arg_queue.pop()

                if ast_queue:
                    ast = ast_queue.pop()
                    repl = ast

                    args = rep_queue[-len(ast.args):]
                    del rep_queue[-len(ast.args):]

                    # Check if replacement occurred.
                    if any((a is not b for a, b in zip(ast.args, args))):
                        repl = ast.make_like(ast.op, tuple(args))
                        replacements[ast.cache_key] = repl

                    rep_queue.append(repl)

        assert len(arg_queue) == 0, "arg_queue is not empty"
        assert len(ast_queue) == 0, "ast_queue is not empty"
        assert len(rep_queue) == 1, ("rep_queue has unexpected length", len(rep_queue))

        return rep_queue.pop()

    def replace(self, old, new, variable_set=None, leaf_operation=None):   # pylint:disable=unused-argument
        """
        Returns this AST but with the AST 'old' replaced with AST 'new' in its subexpressions.
        """
        self._check_replaceability(old, new)
        replacements = {old.cache_key: new}
        return self.replace_dict(replacements, variable_set=old.variables)

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

        for v in self.leaf_asts():
            if v.cache_key not in var_map and v.op in { 'BVS', 'BoolS', 'FPS' }:
                new_name = 'canonical_%d' % next(counter)
                var_map[v.cache_key] = v._rename(new_name)

        return var_map, counter, self.replace_dict(var_map)

    #
    # This code handles burrowing ITEs deeper into the ast and excavating
    # them to shallower levels.
    #

    def _burrow_ite(self):
        if self.op != 'If':
            # print("i'm not an if")
            return self.swap_args([ (a.ite_burrowed if isinstance(a, Base) else a) for a in self.args ])

        if not all(isinstance(a, Base) for a in self.args):
            # print("not all my args are bases")
            return self

        old_true = self.args[1]
        old_false = self.args[2]

        if old_true.op != old_false.op or len(old_true.args) != len(old_false.args):
            return self

        if old_true.op == 'If':
            # let's no go into this right now
            return self

        if any(a.op in operations.leaf_operations for a in self.args):
            # burrowing through these is pretty funny
            return self

        matches = [ old_true.args[i] is old_false.args[i] for i in range(len(old_true.args)) ]
        if matches.count(True) != 1 or all(matches):
            # TODO: handle multiple differences for multi-arg ast nodes
            # print("wrong number of matches:",matches,old_true,old_false)
            return self

        different_idx = matches.index(False)
        inner_if = If(self.args[0], old_true.args[different_idx], old_false.args[different_idx])
        new_args = list(old_true.args)
        new_args[different_idx] = inner_if.ite_burrowed
        # print("replaced the",different_idx,"arg:",new_args)
        return old_true.__class__(old_true.op, new_args, length=self.length)

    def _excavate_ite(self):
        ast_queue = [iter([self])]
        arg_queue = []
        op_queue = []

        while ast_queue:
            try:
                ast = next(ast_queue[-1])

                if not isinstance(ast, Base):
                    arg_queue.append(ast)
                    continue

                if ast.op in operations.leaf_operations:
                    arg_queue.append(ast)
                    continue

                if ast.annotations:
                    arg_queue.append(ast)
                    continue

                op_queue.append(ast)
                ast_queue.append(iter(ast.args))

            except StopIteration:
                ast_queue.pop()

                if op_queue:
                    op = op_queue.pop()

                    args = arg_queue[-len(op.args):]
                    del arg_queue[-len(op.args):]

                    ite_args = [isinstance(a, Base) and a.op == 'If' for a in args]

                    if op.op == 'If':
                        # if we are an If, call the If handler so that we can take advantage of its simplifiers
                        excavated = If(*args)

                    elif ite_args.count(True) == 0:
                        # if there are no ifs that came to the surface, there's nothing more to do
                        excavated = op.swap_args(args, simplify=True)

                    else:
                        # this gets called when we're *not* in an If, but there are Ifs in the args.
                        # it pulls those Ifs out to the surface.
                        cond = args[ite_args.index(True)].args[0]
                        new_true_args = []
                        new_false_args = []

                        for a in args:
                            if not isinstance(a, Base) or a.op != 'If':
                                new_true_args.append(a)
                                new_false_args.append(a)
                            elif a.args[0] is cond:
                                new_true_args.append(a.args[1])
                                new_false_args.append(a.args[2])
                            elif a.args[0] is Not(cond):
                                new_true_args.append(a.args[2])
                                new_false_args.append(a.args[1])
                            else:
                                # weird conditions -- giving up!
                                excavated = op.swap_args(args, simplify=True)
                                break

                        else:
                            excavated = If(cond, op.swap_args(new_true_args, simplify=True),
                                           op.swap_args(new_false_args, simplify=True))

                    # continue
                    arg_queue.append(excavated)

        assert len(op_queue) == 0, "op_queue is not empty"
        assert len(ast_queue) == 0, "ast_queue is not empty"
        assert len(arg_queue) == 1, ("arg_queue has unexpected length", len(arg_queue))

        return arg_queue.pop()

    @property
    def ite_burrowed(self):
        """
        Returns an equivalent AST that "burrows" the ITE expressions as deep as possible into the ast, for simpler
        printing.
        """
        if self._burrowed is None:
            self._burrowed = self._burrow_ite()  # pylint:disable=attribute-defined-outside-init
            self._burrowed._burrowed = self._burrowed  # pylint:disable=attribute-defined-outside-init
        return self._burrowed

    @property
    def ite_excavated(self):
        """
        Returns an equivalent AST that "excavates" the ITE expressions out as far as possible toward the root of the
        AST, for processing in static analyses.
        """
        if self._excavated is None:
            self._excavated = self._excavate_ite()  # pylint:disable=attribute-defined-outside-init

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
            if b in self._errored or b.is_smt_backend:
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
        # import ipdb; ipdb.set_trace()
        return backends.concrete.handles(self)

    @property
    def uninitialized(self):
        """
        Whether this AST comes from an uninitialized dereference or not. It's only used in under-constrained symbolic
        execution mode.

        :returns:                   True/False/None (unspecified).
        """

        #TODO: It should definitely be moved to the proposed Annotation backend.

        return self._uninitialized

    @property
    def uc_alloc_depth(self):
        """
        The depth of allocation by lazy-initialization. It's only used in under-constrained symbolic execution mode.

        :returns:                   An integer indicating the allocation depth, or None if it's not from lazy-initialization.
        """
        # TODO: It should definitely be moved to the proposed Annotation backend.

        return self._uc_alloc_depth

    #
    # Backwards compatibility crap
    #

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
    if isinstance(e, Base) and e.op in operations.leaf_operations:
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

from ..errors import BackendError, ClaripyOperationError, ClaripyReplacementError
from .. import operations
from ..backend_manager import backends
from ..ast.bool import If, Not, BoolS
from ..ast.bv import BV
from .. import simplifications
