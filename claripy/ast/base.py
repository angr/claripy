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

def _is_eager(a):
    if isinstance(a, (int, long, bool, RM, FSort)):
        return True
    elif isinstance(a, Base):
        return a.eager
    else:
        return False

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

    __slots__ = [ 'op', 'args', 'variables', 'symbolic', '_objects', '_collapsible', '_hash', '_simplified', '_cache_key', '_errored', 'eager', 'length' ]
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
        @param eager: whether or not to evaluate future parent ASTs eagerly.
        '''
        if any(not isinstance(a, (str, int, long, bool, Base, BackendObject, FSort)) for a in args):
            #import ipdb; ipdb.set_trace()
            raise ClaripyTypeError("arguments %s contain an unknown type to claripy.Base" % (args,))

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

    #pylint:disable=attribute-defined-outside-init
    def __a_init__(self, op, args, variables=None, symbolic=None, length=None, collapsible=None, simplified=0, errored=None, eager=False, add_variables=None): #pylint:disable=unused-argument
        '''
        Initializes an AST. Takes the same arguments as Base.__new__()
        '''
        self.op = op
        self.args = args
        self.length = length
        self.variables = frozenset(variables)
        self.symbolic = symbolic
        self.eager = eager

        self._collapsible = True if collapsible is None else collapsible
        self._errored = errored if errored is not None else set()

        self._simplified = simplified
        self._cache_key = ASTCacheKey()

        if self.op != 'I' and all(_is_eager(a) for a in self.args):
            model = self.model
            if model is not self:
                self.op = 'I'
                self.args = (model,)

                # Usually `eagerness` should be passed on. However, type of the model might be different than its
                # arguments. In VSA, for instance, a union of two BVVs can lead to a StridedInterval instance, where
                # BVVs should be evaluated eagerly while StridedIntervals should not be, Hence we are rechecking if the
                # model itself should be eagerly evaluated and property set the eager property here.
                self.eager = _is_eager(model)

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

    def _should_collapse(self):
        '''
        This is a helper function that checks if the AST is "collapsible". It returns
        False if there is some reason to keep it from being collapsed. For example,
        an AST that contains only one StridedInterval in its immediate arguments should
        not be collapsed, because the VSA does tricky things to avoid losing precision.
        '''
        raw_args = self.arg_models()
        types = [ type(a) for a in raw_args ]

        #l.debug("In should_collapse()")

        if types.count(Base) != 0 and not all((a._collapsible for a in raw_args if isinstance(a, Base))):
                #l.debug("... not collapsing for op %s because ASTs are present.", self.op)
                return False

        if self.op in operations.not_invertible:
            #l.debug("... collapsing the AST for operation %s because it's not invertible", self.op)
            return True

        constants = sum((types.count(t) for t in (int, long, bool, str, bv.BVV)))
        if constants == len(raw_args):
            #l.debug("... collapsing the AST for operation %s because it's full of constants", self.op)
            return True

        if len([ a for a in raw_args if isinstance(a, StridedInterval) and a.is_integer]) > 1:
            #l.debug("... collapsing the AST for operation %s because there are more than two SIs", self.op)
            return True

        #
        # More complex checks probably go here.
        #

        # Reversible; don't collapse!
        #l.debug("not collapsing the AST for operation %s!", self.op)
        return False

    @property
    def collapsed(self):
        '''
        A collapsed version of the AST, if the AST *can* be collapsed.
        '''
        if self._should_collapse() and self._collapsible:
            #l.debug("Collapsing!")
            r = self.model
            if not isinstance(r, Base):
                if isinstance(self, Bits):
                    return self.__class__('I', args=(r,), length=len(self), variables=self.variables, symbolic=self.symbolic)
                else:
                    return self.__class__('I', args=(r,), variables=self.variables, symbolic=self.symbolic)
            else:
                return r
        else:
            return self

    @property
    def simplified(self):
        '''
        A lightly simplified version of the AST (simplify level 1). This basically
        just cancels out two Reverse operations, if they are present. Later on, it will hopefully
        do more.
        '''

        if self._simplified:
            return self

        if self.op in operations.reverse_distributable and all((isinstance(a, Base) for a in self.args)) and set((a.op for a in self.args)) == { 'Reverse' }:
            inner_a = self.make_like(self.op, tuple(a.args[0] for a in self.args)).simplified
            o = self.make_like('Reverse', (inner_a,), collapsible=True).simplified
            o._simplified = Base.LITE_SIMPLIFY
            return o

        # self = self.make_like(self._claripy, self.op, tuple(a.reduced if isinstance(a, Base) else a for a in self.args))

        return self

    @property
    def reduced(self):
        '''
        A simplified, collapsed version of the AST.
        '''
        a = self.simplified
        if isinstance(a, Base):
            return a.collapsed
        else:
            return a

    # No more size in Base

    @property
    def cardinality(self):
        t = type(self.model)

        if t in (int, long, bool, str, bv.BVV):
            return 1

        elif t in (vsa.IfProxy, vsa.StridedInterval, vsa.ValueSet, vsa.DiscreteStridedIntervalSet):
            return self.model.cardinality

        else:
            raise NotImplementedError("'cardinality' is not supported in modes other than static mode")

    #
    # Functionality for resolving to model objects
    #

    def arg_models(self):
        '''
        Helper function to return the model (i.e., non-AST) objects of the arguments.
        '''
        return [ (a.model if isinstance(a, Base) else a) for a in self.args ]

    def resolved(self, result=None):
        '''
        Returns a model object (i.e., an object that is the result of all the operations
        in the AST), if there is a backend that can handle this AST. Otherwise, return
        itself.

        @arg result: a Result object, for resolving symbolic variables using the
                     concrete backend.
        '''
        for b in _model_backends:
            try: return self.resolved_with(b, result=result)
            except BackendError: self._errored.add(b)
        l.debug("all model backends failed for op %s", self.op)
        return self

    @property
    def model(self):
        '''
        The model object (the result of the operation represented by this AST).
        '''
        r = self.resolved()
        return r

    def resolved_with(self, b, result=None):
        '''
        Returns the result of carrying out the operation of this AST with the
        specified backend.

        @arg b: the backend to resolve with
        @arg result: a Result object, for resolving symbolic variables using the
                     concrete backend
        '''
        if b in self._errored and result is None:
            raise BackendError("%s already failed" % b)

        #l.debug("trying evaluation with %s", b)
        return b.call(self, result=result)

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

        self = self.reduced

        if not isinstance(self.model, Base):
            if inner:
                if isinstance(self.model, bv.BVV):
                    if self.model.value < 10:
                        val = format(self.model.value, '')
                    else:
                        val = format(self.model.value, '#x')
                    return val + ('#' + str(self.model.bits) if explicit_length else '')
                else:
                    return repr(self.model)
            else:
                return '<{} {}>'.format(self._type_name(), self.model)
        else:
            try:
                if self.op in operations.reversed_ops:
                    op = operations.reversed_ops[self.op]
                    args = self.args[::-1]
                else:
                    op = self.op
                    args = self.args

                if op == 'BitVec' and inner:
                    value = args[0]
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
        if self.op == 'BitVec':
            return 0
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
                r = self.make_like(self.op, tuple(new_args)).reduced
            else:
                r = self

        replacements[hash_key] = r
        return r


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

    def identical(self, o):
        '''
        Returns True if 'o' can be easily determined to be identical to this AST.
        Otherwise, return False. Note that the AST *might* still be identical (i.e.,
        if it were simplified via Z3), but it's hard to quickly tell that.
        '''
        return is_identical(self, o)

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

            if arg_a.op in ('I', 'BitVec', 'FP'):
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
        if not isinstance(new, Bool):
            if old.size() != new.size():
                raise ClaripyOperationError('replacements must have matching sizes')
        return self._replace(old, new)

    def _identify_vars(self, all_vars, counter):
        if self.op == 'BitVec':
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
# Unbound methods
#

def is_identical(*args):
    '''
    Attempts to check if the underlying models of the expression are identical,
    even if the hashes match.

    This process is somewhat conservative: False does not necessarily mean that
    it's not identical; just that it can't (easily) be determined to be identical.
    '''
    if not all([isinstance(a, Base) for a in args]):
        return False

    if len(set(hash(a) for a in args)) == 1:
        return True

    first = args[0]
    identical = None
    for o in args:
        for b in _all_backends:
            try:
                i = b.identical(first, o)
                if identical is None:
                    identical = True
                identical &= i is True
            except BackendError:
                pass

        if not identical:
            return False

    return identical is True

def model_object(e, result=None):
    for b in _all_backends:
        try: return b.convert(e, result=result)
        except BackendError: pass
    raise ClaripyTypeError('no model backend can convert expression')

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

from ..errors import BackendError, ClaripyOperationError, ClaripyRecursionError, ClaripyTypeError
from .. import operations
from .. import bv, vsa
from ..fp import RM, FSort
from ..vsa import StridedInterval
from ..backend_object import BackendObject
from .. import _all_backends, _model_backends
from ..ast.bits import Bits
from ..ast.bool import Bool
from ..ast.bv import BV
