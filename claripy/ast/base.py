"""
Module containing Base AST class and associated functions.
"""

import sys
import logging
import weakref
import itertools
import ana

l = logging.getLogger("claripy.ast")

#pylint:enable=unused-argument
#pylint:disable=unidiomatic-typecheck


#
# Deduplication and caching
#

class ASTCacheKey(object):
    """
    Class used as a key for dictionaries of ASTs, typically for replacement
    lists.
    """
    def __init__(self, a):
        self.ast = a

    def __hash__(self):
        return hash(self.ast)

    def __eq__(self, other):
        return hash(self.ast) == hash(other.ast)

    def __repr__(self):
        return "<Key " + self.ast.__repr__()[1:]

def _concrete_evaluate(expr):
    if not expr._eager or expr.op in operations.backend_creation_operations:
        return expr

    try:
        return backends.concrete.simplify(expr)
    except BackendError:
        expr._eager = False
        return expr

def _simplify(expr):
    s = simplifier.simplify(expr.structure)
    return expr.swap_structure(simplifier.simplify(expr.structure), apply_filters=False)._deduplicate() if s is not expr.structure else expr

_hash_cache = weakref.WeakValueDictionary()
def _deduplicate(expr):
    return _hash_cache.setdefault(hash(expr), expr)

#
# AST variable naming
#

var_counter = itertools.count()
_unique_names = True

def _make_name(name, size, explicit_name=False, prefix=""):
    """
    Create a unique fresh name.

    :param name: (Base) Name of variable.
    :param size: An integer.
    :param explicit_name: If True, just return the `name` instead of generating
                          a fresh name. False by default.
    :param prefix: Prefix of the generated name.

    :returns: A fresh name if `explicit_name` is False, else just `name`.
    """
    if _unique_names and not explicit_name:
        return "%s%s_%d_%d" % (prefix, name, var_counter.next(), size)
    else:
        return name

class Base(ana.Storable):
    """
    An AST tracks a tree of operations on arguments. It has the following properties:

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

    __slots__ = [
        # '__weakref__', (in ana.Storable)
        'structure', 'outer_annotations', 'filters',
        'cache_key', '_hash', '_eager',
        '_simplified', '_excavated', '_burrowed',
    ]

    DEFAULT_FILTERS = ( _concrete_evaluate, _simplify )

    def __init__(self, structure, outer_annotations=frozenset(), filters=None, _eager=True):
        """
        This is called when you create a new Base object, whether directly or through an operation.
        It finalizes the arguments (see the _finalize function, above) and then computes
        a hash. If an AST of this hash already exists, it returns that AST. Otherwise,
        it creates, initializes, and returns the AST.

        :param structure:            The structure of the AST (operation, arguments, etc).
        :param outer_annotations:    A frozenset of annotations applied onto this AST.
        :param filters:              Filter functions to run on this AST after every operation.
        :param _eager:               Whether or not this AST could be eager evaluated
        """

        # store the AST structure
        self.structure = structure
        if not isinstance(structure, ASTStructure):
            raise ClaripyTypeError("Invalid structure encountered in expression constructor.")

        # whether this AST could be eager evaluated
        self._eager = _eager

        # the list of annotations applied to the outer level of the AST
        self.outer_annotations = outer_annotations

        # these are filters that get applied to the AST at every operation
        self.filters = Base.DEFAULT_FILTERS if filters is None else filters

        # a cache key, to use when storing this AST in dicts (to survive bucket collisions)
        self.cache_key = ASTCacheKey(self)

        # references to various transformations of this AST
        self._excavated = None
        self._burrowed = None
        self._simplified = None

        # the hash
        self._hash = None

    def _deduplicate(self):
        return _deduplicate(self)

    @property
    def uc_alloc_depth(self):
        """
        The depth of allocation by lazy-initialization. It's only used in under-constrained symbolic execution mode.

        :return: An integer indicating the allocation depth, or None if it's not from lazy-initialization.
        """
        raise Exception("TODO")

    @property
    def uninitialized(self):
        """
        Whether this AST comes from an uninitialized dereference or not. It's only used in under-constrained symbolic
        execution mode.
        """
        return self.structure.uninitialized

    @property
    def op(self):
        """
        The operation of the AST.
        """
        return self.structure.op

    @property
    def args(self):
        """
        The arguments of the AST, as AST-wrapped structures.
        """
        return tuple((backends.ast_type.convert(a)(
            a, outer_annotations=self.outer_annotations, filters=self.filters
        )._deduplicate() if isinstance(a, ASTStructure) else a) for a in self.structure.args)

    @property
    def inline_annotations(self):
        """
        The inline annotations on the AST.
        """
        return self.structure.annotations

    @property
    def ite_burrowed(self):
        """
        Returns an equivalent AST that "burrows" the ITE expressions as deep as possible into the ast, for simpler
        printing.
        """
        return self.swap_structure(backends.ite_burrower.convert(self.structure))

    @property
    def ite_excavated(self):
        """
        Returns an equivalent AST that "excavates" the ITE expressions out as far as possible toward the root of the
        AST, for processing in static analyses.
        """
        return self.swap_structure(backends.ite_excavator.convert(self.structure))

    @property
    def variables(self):
        try:
            return backends.variables.convert(self)
        except BackendError:
            l.critical("BackendVariables failed to compute variables of AST %s", self)
            return frozenset()

    @property
    def symbolic(self):
        try:
            return backends.symbolic.convert(self)
        except BackendError:
            l.critical("BackendSymbolic failed to compute symbolicity of AST %s", self)
            return None

    @property
    def length(self):
        try:
            return backends.length.convert(self)
        except BackendError:
            return None

    @property
    def depth(self):
        """
        The depth of this tree. For example, an AST representing (a+(b+c)) would have a depth of 2.
        """
        return self.structure.depth

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
        """
        The UUID of the AST (currently equal to its hash).
        """
        return self.ana_uuid

    def _ana_getstate(self):
        """
        Support for ANA serialization.
        """
        return self.structure, self.outer_annotations, self.filters, self._eager, self._hash

    def _ana_setstate(self, state):
        """
        Support for ANA deserialization.
        """
        structure, outer_annotations, filters, _eager, h = state
        Base.__init__(self, structure, outer_annotations=outer_annotations,
                      filters=filters, _eager=_eager)
        self._hash = h
        _hash_cache[h] = self

    def _apply_filters(self):
        new_ast = self
        for f in new_ast.filters:
            try:
                #l.debug("Running filter %s.", f)
                old_ast = new_ast
                new_ast = f(new_ast) #if hasattr(f, '__call__') else f.convert(new_ast)
                if old_ast is not new_ast:
                    new_ast = new_ast._deduplicate()
            except BackendError:
                l.warning("Ignoring BackendError during AST filter application.")
        return new_ast

    def __hash__(self):
        if self._hash is None:
            self._hash = self._calc_hash()
        return self._hash

    def _calc_hash(self):
        """
        Calculates the hash of an AST.

        """
        return hash((self.structure, self.outer_annotations, self.filters))

    def globalize(self):
        """
        Makes this AST globally storable and referenceable. "Globally" here refers
        to being transferrable between different processes and so forth.
        """
        self.structure.make_uuid()

    #
    # AST modifications.
    #

    def swap_args(self, new_args):
        """
        This returns the same AST, with the arguments swapped out for new_args.
        """

        return self.swap_structure(self.structure.swap_args(tuple((a.structure if isinstance(a, Base) else a) for a in new_args)))

    def swap_structure(self, structure, apply_filters=True, _eager=None, filters=None):
        """
        This returns the same AST, with the structure swapped out for a different one.
        """

        a = self.__class__(
            structure, self.outer_annotations,
            filters=self.filters if filters is None else filters,
            _eager=self._eager if _eager is None else _eager
        )._deduplicate()
        return a._apply_filters() if apply_filters else a

    def swap_inline_annotations(self, new_tuple):
        """
        Replaces annotations on this AST.

        :param new_tuple: the tuple of annotations to replace the old annotations with
        :returns: a new AST, with the annotations added
        """
        return self.swap_structure(self.structure.swap_annotations(new_tuple))

    def swap_outer_annotations(self, new_tuple, apply_filters=False):
        """
        Replaces annotations on this AST.

        :param new_tuple: the tuple of annotations to replace the old annotations with
        :returns: a new AST, with the annotations added
        """
        a = self.__class__(self.structure, new_tuple, filters=self.filters, _eager=self._eager)._deduplicate()
        return a._apply_filters() if apply_filters else a

    def replace(self, old, new):
        """
        Returns an AST with all instances of the AST 'old' replaced with AST 'new'.
        """
        replacements = { old.structure: new.structure }
        return self.swap_structure(self.structure.replace(replacements), _eager=True)

    def replace_dict(self, replacements):
        """
        Returns an AST with ASTStructure replacements from the replacements dictionary applied.
        """
        return self.swap_structure(self.structure.replace(replacements), _eager=True)

    def canonicalize(self):
        """
        Pass-through to ASTStructure.canonicalize.
        """

        vm, s = self.structure.canonicalize()
        return vm, self.swap_structure(s)

    #
    # Annotations
    #

    def annotate(self, *args):
        """
        WARNING: DEPRECATED. USE annotate_outer INSTEAD.
        Appends annotations to this AST.

        :param args: the tuple of annotations to append (variadic positional args)
        :returns: a new AST, with the annotations added
        """
        l.critical("Base.annotate is deprecated. Use Base.annotate_outer.")
        print "Base.annotate is deprecated. Use Base.annotate_outer."
        return self.annotate_outer(self, *args)

    def annotate_inline(self, *args):
        """
        Appends annotations to this AST's structure.

        :param args: the tuple of annotations to append (variadic positional args)
        :returns: a new AST, with the annotations added
        """
        return self.swap_structure(self.structure.annotate(*args))

    def annotate_outer(self, *args):
        """
        Appends annotations to this AST.

        :param args: the tuple of annotations to append (variadic positional args)
        :returns: a new AST, with the annotations added
        """
        return self.swap_outer_annotations(self.outer_annotations.union(args))

    #
    # Viewing and debugging
    #

    def dbg_repr(self, prefix=None):
        """
        Print the AST for debugging purposes.

        :param prefix: Optional prefix to insert before printing each node of
                       the AST.
        :raises: ClaripyRecursionError
        """
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

    def shallow_repr(self, max_depth=8):
        """
        Returns a representation of the AST up to a maximum depth `max_depth`
        as a string.
        """
        return self.__repr__(max_depth=max_depth)

    def __repr__(self, **kwargs):
        return "<%s%s %s>" % (self.__class__.__name__, str(self.length) if self.length is not None else '', self.structure.repr(**kwargs))

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
        example, the following was previously a common error:

            a,b = two ASTs
            if a == b:
                do something

        The problem is that `a == b` would return an AST, because an AST can be symbolic
        and there could be no way to actually know the value of that without a
        constraint solve. This caused tons of issues.
        """
        raise ClaripyOperationError('testing Expressions for truthiness does not do what you want, as these expressions can be symbolic')

    #
    # these are convenience operations
    #

    @property
    def singlevalued(self):
        """
        True if the AST takes on only one value.
        """
        return backends.first_successful('singlevalued', self)

    @property
    def multivalued(self):
        """
        True if the AST takes on multiple values.
        """
        return backends.first_successful('multivalued', self)

    @property
    def cardinality(self):
        """
        Returns the number of values the AST is estimated to take on.
        """
        return backends.first_successful('cardinality', self)

    @property
    def concrete(self):
        """
        True if the AST is concrete.
        """
        return backends.concrete.handles(self)

    def __reduce__(self):
        return (_unpickle_structure, (self.structure, self.outer_annotations, self.filters))

    #
    # Backwards compatibility crap
    #

    @property
    def _model_vsa(self):
        return backends.vsa.convert(self)

    @property
    def _model_concrete(self):
        return backends.concrete.convert(self)

    @property
    def _model_z3(self):
        return backends.z3.convert(self)

def _unpickle_structure(structure, outer_annotations, filters):
    return Base(structure, outer_annotations=outer_annotations, filters=filters)._deduplicate()

#
# Simplification helper
#

def simplify(e):
    """
    Attempt to simply the expression with the first non-errored backend.
    """
    if isinstance(e, Base) and e.op == 'I':
        return e

    s = backends.first_successful('simplify', e)
    if s is None:
        l.debug("Unable to simplify expression")
        return e
    else:
        return s

#
# Operation support
#

_type_fixers = { }

def make_op(name, arg_types, return_type, do_coerce=True, structure_postprocessor=None, expression_postprocessor=None):
    """
    Creates a claripy AST operator.

    :param name: Name of the operator.
    :param arg_types: Types of the arguments that the operator accepts. Either a
                      tuple/list of types, or a single type (indicating a
                      variable number of arguments with the same type)
    :param return_type: The return type of the operator.
    :param do_coerce: True if type coercion should be attempted. True by default.
    :param structure_postprocessor: Callable that takes the ASTStructure after
                                    types have been coerced.
    :param expression_postprocessor: Callable that takes the return object
                                     (of type return_type) immediately before
                                     it is returned.

    :returns: A claripy AST operator than can be used to construct ASTs.

    :raises: ClaripyOperationError
    """
    if type(arg_types) in (tuple, list): #pylint:disable=unidiomatic-typecheck
        expected_num_args = len(arg_types)
    elif type(arg_types) is type: #pylint:disable=unidiomatic-typecheck
        expected_num_args = None
    else:
        raise ClaripyOperationError("op {} got weird arg_types".format(name))

    if expected_num_args is None:
        def _type_fixer(args, reference):
            return tuple(
                a if isinstance(a, arg_types) else _type_fixers[type(a)](a, reference)
                for a in args
            )
    else:
        def _type_fixer(args, reference):
            if len(args) != expected_num_args:
                raise ClaripyTypeError("Operation {} takes exactly {} arguments ({} given)".format(name, expected_num_args, len(args)))
            return tuple(
                a if isinstance(a, t) else _type_fixers[type(a)](a, reference)
                for a,t in zip(args, arg_types)
            )

    def _op(*args):
        if do_coerce:
            reference = next(a for a in args if isinstance(a, Base))
            try:
                fixed_args = _type_fixer(args, reference)
            except KeyError:
                return NotImplemented
        else:
            fixed_args = tuple(a for a in args)

        new_structure = get_structure(name, tuple(a.structure if isinstance(a, Base) else a for a in fixed_args))
        if structure_postprocessor is not None:
            new_structure = structure_postprocessor(new_structure)

        ast_args = [ a for a in args if isinstance(a, Base) ]
        new_outer_annotations = frozenset().union(*(a.outer_annotations for a in ast_args))
        new_eager = all(a._eager for a in ast_args)
        nondefault_filters = [ a.filters for a in ast_args if a.filters is not Base.DEFAULT_FILTERS ]
        if nondefault_filters:
            new_filters = max(nondefault_filters, key=len)
        else:
            new_filters = None

        e = return_type(new_structure, new_outer_annotations, filters=new_filters, _eager=new_eager)._deduplicate()._apply_filters()
        if expression_postprocessor is not None:
            e = expression_postprocessor(e)
        return e

    return _op

def make_reversed_op(op_func):
    def _reversed_op(*args):
        return op_func(*args[::-1])
    return _reversed_op

from ..errors import BackendError, ClaripyOperationError, ClaripyRecursionError, ClaripyTypeError
from ..backend_manager import backends
from .structure import get_structure, ASTStructure
from .. import operations
from ..simplifier import simplifier
