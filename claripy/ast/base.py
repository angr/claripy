import os
import sys
import struct
import weakref
import hashlib
import itertools
import cPickle as pickle

import logging
l = logging.getLogger("claripy.ast")

import ana

if os.environ.get('WORKER', False):
    WORKER = True
else:
    WORKER = False

md5_unpacker = struct.Struct('2Q')

#pylint:enable=unused-argument
#pylint:disable=unidiomatic-typecheck

def _inner_repr(a, **kwargs):
    if isinstance(a, Base):
        return a.__repr__(inner=True, **kwargs)
    else:
        return repr(a)

class ASTCacheKey(object): pass

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
    '''
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
    '''

    __slots__ = [ 'op', 'args', 'variables', 'symbolic', '_objects', '_collapsible', '_hash', '_simplified', '_cache_key', '_errored', '_eager_backends', 'length', '_excavated', '_burrowed' ]
    _hash_cache = weakref.WeakValueDictionary()

    FULL_SIMPLIFY=1
    LITE_SIMPLIFY=2
    UNSIMPLIFIED=0

    def __new__(cls, op, args, **kwargs):
        '''
        This is called when you create a new Base object, whether directly or through an operation.
        It finalizes the arguments (see the _finalize function, above) and then computes
        a hash. If an AST of this hash already exists, it returns that AST. Otherwise,
        it creates, initializes, and returns the AST.

        @param op: the AST operation ('__add__', 'Or', etc)
        @param args: the arguments to the AST operation (i.e., the objects to add)
        @param variables: the symbolic variables present in the AST (default: empty set)
        @param symbolic: a flag saying whether or not the AST is symbolic (default: False)
        @param length: an integer specifying the length of this AST (default: None)
        @param collapsible: a flag of whether or not Claripy can feel free to collapse this AST.
                            This is mostly used to keep Claripy from collapsing Reverse operations,
                            so that they can be undone with another Reverse.
        @param simplified: a measure of how simplified this AST is. 0 means unsimplified, 1 means
                           fast-simplified (basically, just undoing the Reverse op), and 2 means
                           simplified through z3.
        @param errored: a set of backends that are known to be unable to handle this AST.
        @param eager_backends: a list of backends with which to attempt eager evaluation
        '''

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

        eager_backends = list(_eager_backends) if 'eager_backends' not in kwargs else kwargs['eager_backends']

        if eager_backends is not None and op not in operations.leaf_operations:
            for eb in eager_backends:
                try:
                    return eb._abstract(eb.call(op, args))
                except BackendError:
                    eager_backends.remove(eb)

            # if we can't be eager anymore, null out the eagerness
            kwargs['eager_backends'] = None

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
        '''
        Calculates the hash of an AST, given the operation, args, and kwargs.

        @param op: the operation
        @param args: the arguments to the operation
        @param kwargs: a dict including the 'symbolic', 'variables', and 'length' items

        @returns a hash
        '''
        to_hash = (op, tuple(str(a) if type(a) in (int, long) else hash(a) for a in args), k['symbolic'], hash(k['variables']), str(k.get('length', None)))
        # Why do we use md5 when it's broken? Because speed is more important
        # than cryptographic integrity here. Then again, look at all those
        # allocations we're doing here... fast python is painful.
        hd = hashlib.md5(pickle.dumps(to_hash, -1)).digest()
        return md5_unpacker.unpack(hd)[0] # 64 bits

    def _get_hashables(self):
        return self.op, tuple(str(a) if type(a) in (int, long) else hash(a) for a in self.args), self.symbolic, hash(self.variables), str(self.length)

    #pylint:disable=attribute-defined-outside-init
    def __a_init__(self, op, args, variables=None, symbolic=None, length=None, collapsible=None, simplified=0, errored=None, eager_backends=None, add_variables=None): #pylint:disable=unused-argument
        '''
        Initializes an AST. Takes the same arguments as Base.__new__()
        '''
        self.op = op
        self.args = args
        self.length = length
        self.variables = frozenset(variables)
        self.symbolic = symbolic
        self._eager_backends = eager_backends

        self._collapsible = True if collapsible is None else collapsible
        self._errored = errored if errored is not None else set()

        self._simplified = simplified
        self._cache_key = ASTCacheKey()
        self._excavated = None
        self._burrowed = None

        if len(args) == 0:
            raise ClaripyOperationError("AST with no arguments!")

        #if self.op != 'I':
        #    for a in args:
        #        if not isinstance(a, Base) and type(a) not in (int, long, bool, str, unicode):
        #            import ipdb; ipdb.set_trace()
        #            l.warning(ClaripyOperationError("Un-wrapped native object of type %s!" % type(a)))
    #pylint:enable=attribute-defined-outside-init

    def make_uuid(self, uuid=None):
        '''
        This overrides the default ANA uuid with the hash of the AST. UUID is slow,
        and we'll soon replace it from ANA itself, and this will go away.

        @returns a string representation of the AST hash.
        '''
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

    #
    # Serialization support
    #

    def _ana_getstate(self):
        '''
        Support for ANA serialization.
        '''
        return self.op, self.args, self.length, self.variables, self.symbolic, self._hash
    def _ana_setstate(self, state):
        '''
        Support for ANA deserialization.
        '''
        op, args, length, variables, symbolic, h = state
        Base.__a_init__(self, op, args, length=length, variables=variables, symbolic=symbolic)
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
        return type(self)(*args, **kwargs)

    @property
    def cardinality(self):
        for b in _all_backends:
            try: return b.cardinality(self)
            except BackendError: pass

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

    def __repr__(self, inner=False, explicit_length=False):
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
                value = 'if {} then {} else {}'.format(_inner_repr(args[0]),
                                                       _inner_repr(args[1]),
                                                       _inner_repr(args[2]))
                if inner:
                    value = '({})'.format(value)
            elif op == 'Not':
                value = '!{}'.format(_inner_repr(args[0]))
            elif op == 'Extract':
                value = '{}[{}:{}]'.format(_inner_repr(args[2]), args[0], args[1])
            elif op == 'ZeroExt':
                value = '0#{} .. {}'.format(args[0], _inner_repr(args[1]))
                if inner:
                    value = '({})'.format(value)
            elif op == 'Concat':
                value = ' .. '.join(_inner_repr(a, explicit_length=True) for a in self.args)
            elif len(args) == 2 and op in operations.infix:
                value = '{} {} {}'.format(_inner_repr(args[0]),
                                          operations.infix[op],
                                          _inner_repr(args[1]))
                if inner:
                    value = '({})'.format(value)
            else:
                value = "{}({})".format(op,
                                        ', '.join(_inner_repr(a) for a in args))

            if not inner:
                value = '<{} {}>'.format(self._type_name(), value)

            return value
        except RuntimeError:
            e_type, value, traceback = sys.exc_info()
            raise ClaripyRecursionError, ("Recursion limit reached during display. I sorry.", e_type, value), traceback

    @property
    def depth(self):
        '''
        The depth of this AST. For example, an AST representing (a+(b+c)) would have
        a depth of 2.
        '''
        ast_args = [ a for a in self.args if isinstance(a, Base) ]
        return 1 + (max(a.depth for a in ast_args) if len(ast_args) > 0 else 1)

    @property
    def recursive_children_asts(self):
        for a in self.args:
            if isinstance(a, Base):
                l.debug("Yielding AST %s with hash %s with %d children", a, hash(a), len(a.args))
                yield a
                for b in a.recursive_children_asts:
                    yield b

    def dbg_is_looped(self, seen=None, checked=None):
        seen = set() if seen is None else seen
        checked = set() if checked is None else checked

        seen.add(hash(self))
        for a in self.recursive_children_asts:
            l.debug("Checking AST with hash %s for looping", hash(a))
            if hash(a) in seen:
                return a
            elif hash(a) in checked:
                return False
            else:
                for a in self.args:
                    if not isinstance(a, Base):
                        continue

                    r = a.dbg_is_looped(seen=seen, checked=checked)
                    if r is not False: return r
                    else: checked.add(hash(a))

        seen.discard(hash(self))
        return False

    #
    # Various AST modifications (replacements)
    #

    def _replace(self, old, new, replacements=None):
        '''
        A helper for replace().
        '''
        if replacements is None:
            replacements = { hash(old): new }

        hash_key = hash(self)

        if hash_key in replacements:
            r = replacements[hash_key]
        elif not self.variables.issuperset(old.variables):
            r = self
        else:
            new_args = [ ]
            replaced = False

            for a in self.args:
                if isinstance(a, Base):
                    new_a = a._replace(old, new, replacements=replacements)
                    replaced |= hash(new_a) != hash(a)
                else:
                    new_a = a

                new_args.append(new_a)

            if replaced:
                r = self.make_like(self.op, tuple(new_args))
            else:
                r = self

        replacements[hash_key] = r
        return r

    def swap_args(self, new_args, new_length=None):
        '''
        This returns the same AST, with the arguments swapped out for new_args.
        '''

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
        '''
        Splits the AST if its operation is split_on (i.e., return all the arguments).
        Otherwise, return a list with just the AST.
        '''
        if self.op in split_on: return list(self.args)
        else: return [ self ]

    # we don't support iterating over Base objects
    def __iter__(self):
        '''
        This prevents people from iterating over ASTs.
        '''
        raise ClaripyOperationError("Please don't iterate over, or split, AST nodes!")

    def __nonzero__(self):
        '''
        This prevents people from accidentally using an AST as a condition. For
        example, the following was previously common:

            a,b = two ASTs
            if a == b:
                do something

        The problem is that `a == b` would return an AST, because an AST can be symbolic
        and there could be no way to actually know the value of that without a
        constraint solve. This caused tons of issues.
        '''
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
        '''
        Returns an AST with all instances of the AST 'old' replaced with AST 'new'
        '''
        if not isinstance(old, Base) or not isinstance(new, Base):
            raise ClaripyOperationError('replacements must be AST nodes')
        if type(old) is not type(new):
            raise ClaripyOperationError('cannot replace type %s ast with type %s ast' % (type(old), type(new)))
        old._check_replaceability(new)
        return self._replace(old, new)

    def _check_replaceability(self, new):
        pass

    def _identify_vars(self, all_vars, counter):
        if self.op == 'BVS':
            if self.args not in all_vars:
                all_vars[self.args] = BV('var_' + str(next(counter)),
                                         self.args[1],
                                         explicit_name=True)
        else:
            for arg in self.args:
                if isinstance(arg, Base):
                    arg._identify_vars(all_vars, counter)

    def canonicalized(self, existing_vars=None, counter=None):
        all_vars = {} if existing_vars is None else existing_vars
        counter = itertools.count() if counter is None else counter
        self._identify_vars(all_vars, counter)

        expr = self
        for old_var, new_var in all_vars.items():
            expr = expr.replace(BV(*old_var, explicit_name=True), new_var)

        return all_vars, expr

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
        '''
        Returns an equivalent AST that "burrows" the ITE expressions
        as deep as possible into the ast, for simpler printing.
        '''
        if self._burrowed is None:
            self._burrowed = self._burrow_ite() #pylint:disable=attribute-defined-outside-init
        return self._burrowed

    @property
    def ite_excavated(self):
        '''
        Returns an equivalent AST that "excavates" the ITE expressions
        out as far as possible toward the root of the AST, for processing
        in static analyses.
        '''
        if self._excavated is None:
            self._excavated = self._excavate_ite() #pylint:disable=attribute-defined-outside-init
        return self._excavated

    #
    # Alright, I give up. Here are some convenience accessors to backend models.
    #

    @property
    def _model_vsa(self):
        try:
            return _backends['BackendVSA'].convert(self)
        except BackendError:
            return self

    @property
    def _model_z3(self):
        try:
            return _backends['BackendZ3'].convert(self)
        except BackendError:
            return self

    @property
    def _model_concrete(self):
        try:
            return _backends['BackendConcrete'].convert(self)
        except BackendError:
            return self

def simplify(e):
    if isinstance(e, Base) and e.op == 'I':
        return e

    for b in _all_backends:
        try:
            s = b.simplify(e)
            s._simplified = Base.FULL_SIMPLIFY
            return s
        except BackendError:
            pass

    l.debug("Unable to simplify expression")
    return e

from ..errors import BackendError, ClaripyOperationError, ClaripyRecursionError
from .. import operations
from ..backend_object import BackendObject
from .. import _all_backends, _eager_backends, _backends
from ..ast.bool import If, Not
from ..ast.bv import BV
