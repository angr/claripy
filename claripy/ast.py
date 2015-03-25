import sys
import weakref
import logging
l = logging.getLogger("claripy.ast")

import ana

#
#
# Finalizer functions for different expressions
#
#
def _finalize(claripy, op, args, kwargs):
    '''
    Each AST is "finalized" by this finalizer function.

    @param op: a string representing the operation of the AST ('__add__', 'ULT', etc)
    @param args: the arguments to the operation
    @kwargs: keyword arguments, such as variables, the length, etc

    The finalizer is responsible for determining the following flags of the new AST:

        variables - the union of the set of variables of the argument ASTS
        symbolic - an OR of the symbolic flag of the arguments
        errored - a set of the backends which *can't* handle this AST
        length - the length (if the AST is a bitvector)

    It calls out to the _finalize_X functions, where X is the operation to convert
    the arguments and keyword arguments to the right types.

    @returns the operation, and updated args and kwargs (as provided by the
             _finalize_X helpers)
    '''
    variables = kwargs.get('variables', None)
    if variables is None:
        variables = frozenset.union(frozenset(), *(a.variables for a in args if isinstance(a, A)))
    kwargs['variables'] = variables

    symbolic = kwargs.get('symbolic', None)
    if symbolic is None:
        symbolic = any((a.symbolic for a in args if isinstance(a, A)))
    kwargs['symbolic'] = symbolic

    errored = kwargs.get('errored', None)
    if errored is None:
        kwargs['errored'] = _finalize_get_errored(args)

    nolength = op == 'I' or op == 'If'
    if '_finalize_' + op in globals():
        o,a,k = globals()['_finalize_' + op](claripy, op, args, kwargs)
    elif op in length_same_operations:
        o,a,k = _finalize_same_length(claripy, op, args, kwargs)
    elif op in length_none_operations:
        o,a,k = op, args, kwargs
        nolength = True
    else:
        raise ClaripyOperationError("no A._finalize_* function found for %s" % op)

    length = k.get('length', None)
    if not nolength and (length is None or length < 0):
        raise ClaripyOperationError("invalid length!")

    k['length'] = length
    k['variables'] = kwargs['variables']
    return o,tuple(a),k


def _arg_size(o):
    '''
    Returns the size of the AST object, or None if 'o' is not an AST object.

    @param o: the object in question
    @returns the length, or None
    '''
    if isinstance(o, A): return o.length
    else: return None

def _typefixer(a, t):
    '''
    This is an implementation of a modiyer for Claripy's half-assed type system.
    It's a helper function for _typechecker, below.

    @param a: the object whose type to "fix". This should be a native object, like an int or a long.
    @param t: a string describing the type, or the type ('I' for int, 'L' for long, 'N' for any number)
    @returns the object, converted to the requested type.
    @raises a ClaripyOperationError if arg can't be converted

    This function was written in some misguided attempt to have a simpler-than-actual type system.
    Don't count on it being around for long.
    '''
    if t in ('I', 'L', 'N'):
        if not type(a) in (int, long):
            raise ClaripyOperationError("argument is not the right type (%s instead of int/long)" % type(a))
        return int(a) if t == 'I' else long(a) if t == 'L' else a
    else:
        if not isinstance(a, t):
            raise ClaripyOperationError("argument is not the right type (%s instead of int/long)" % type(a))
        return a

def _typechecker(op, args, types):
    '''
    This is a helper function for type checking in Claripy. In addition to type
    checking, it also *converts* the arguments (this is used, for example, to make
    sure that all integer arguments are actually ints, and not longs, as having that
    occur will later break Z3).

    @param op: the operation that the arguments that are being checked *for*. This is
               just used for logging
    @param args: a tuple of arguments
    @param types: a tuple of types. These can be actual type objects, or 'I' (for
                  int), 'L' (for long), or 'N' (for any numerical value). I honestly
                  have no idea why this happened like this; it was during a deadline
                  and I'm sure I had a reason, but it seems as awful to me now as it
                  does to you.

    @returns a new tuple of args, with each arg converted to the specified type
    @raises a ClaripyOperationError if an arg can't be converted
    '''
    if len(args) != len(types):
        raise ClaripyOperationError("%d args passed to %s (need %d)" % (len(args), op, len(types)))
    return tuple(_typefixer(a,t) for a,t in zip(args, types))

#pylint:disable=unused-argument

def _finalize_Identical(claripy, op, args, kwargs):
    '''
    Finalizes an AST representing an Identical operation. This sets its length to None.
    '''
    kwargs['length'] = None
    return op, args, kwargs

def _finalize_BoolVal(claripy, op, args, kwargs):
    '''
    Finalizes an AST representing an BoolVal operation. Type enforced:

        BoolVal(bool)
    '''
    args = _typechecker(op, args, (bool,))
    return op, args, kwargs

def _finalize_BitVec(claripy, op, args, kwargs):
    '''
    Finalizes an AST representing a BitVec operation. Type enforced:

        BitVec(str, int)
    '''
    args = _typechecker(op, args, (str, 'I'))
    kwargs['length'] = args[1]
    return op, args, kwargs

def _finalize_BitVecVal(claripy, op, args, kwargs):
    '''
    Finalizes an AST representing a BitVec operation. Type enforced:

        BitVec(str, int)
    '''
    args = _typechecker(op, args, ('N', 'I'))
    if args[1] <= 0:
        raise ClaripyOperationError("Invalid arguments to BitVecVal")
    kwargs['length'] = args[1]
    return op, args, kwargs

def _finalize_If(claripy, op, args, kwargs):
    '''
    Finalizes an AST representing an If.

    An If requires a boolean condition, and at least one case with a length. If both
    cases have lengths, they must be equal.
    '''

    if len(args) != 3:
        raise ClaripyOperationError("If requires a condition and two cases.")

    if _arg_size(args[0]) is not None:
        raise ClaripyOperationError("non-boolean condition passed to If")

    case_lengths = ( _arg_size(args[1]), _arg_size(args[2]) )
    if len(set(case_lengths)) != 1:
        if None not in case_lengths:
            raise ClaripyOperationError("If needs two identically-sized sized")
        else:
            # we need to convert one of the cases to an integer
            if case_lengths[0] is None:
                if type(args[1]) not in (int, long):
                    raise ClaripyOperationError("If received a non-int and an int case.")
                args = (args[0], claripy.BVV(args[1], case_lengths[1]), args[2])
            else:
                if type(args[2]) not in (int, long):
                    raise ClaripyOperationError("If received a non-int and an int case.")
                args = (args[0], args[1], claripy.BVV(args[2], case_lengths[0]))

    lengths = set(_arg_size(a) for a in args[1:]) - { None }
    kwargs['length'] = lengths.pop() if len(lengths) > 0 else None
    return op, args, kwargs

def _finalize_Concat(claripy, op, args, kwargs):
    '''
    Finalizes a Concat AST. All args to the AST must have a length (i.e., be bitvectors).
    '''
    lengths = [ _arg_size(a) for a in args ]
    if None in lengths or len(args) <= 1:
        raise ClaripyOperationError("Concat must have at >= two args, and all must have lengths.")

    kwargs['length'] = sum(lengths)
    return op, args, kwargs

def _finalize_Extract(claripy, op, args, kwargs):
    '''
    Finalizes an Extract operation. Must have two integer arguments (from, to) and an AST.
    '''
    args = _typechecker(op, args, ('I', 'I', A))
    if len(args) != 3 or type(args[0]) not in (int, long) or type(args[1]) not in (int, long):
        raise ClaripyOperationError("Invalid arguments passed to extract!")

    length = args[0]-args[1]+1
    old_length = _arg_size(args[2])
    if length > old_length or args[0] >= old_length or args[1] >= old_length or length <= 0:
        raise ClaripyOperationError("Invalid sizes passed to extract!")

    kwargs['length'] = length
    return op, args, kwargs

def _finalize_ZeroExt(claripy, op, args, kwargs):
    '''
    This is the finalizer for ZeroExtend and SignExtend. Args must be an int and
    an A objects.
    '''
    args = _typechecker(op, args, ('I', A))
    length = _arg_size(args[1])
    if length is None:
        raise ClaripyOperationError("extending an object without a length")

    kwargs['length'] = length + args[0]
    return op, args, kwargs

_finalize_SignExt = _finalize_ZeroExt

def _finalize_Reverse(claripy, op, args, kwargs):
    '''
    This finalizes the Reverse operation.
    '''
    if len(args) != 1:
        raise ClaripyOperationError("Reverse takes exactly one argument")

    length = _arg_size(args[0])
    if length is None or length%8 != 0:
        raise ClaripyOperationError("Argument to reverse must be a multiple of 8 bits long")

    kwargs['length'] = length
    return op, args, kwargs

def _finalize_same_length(claripy, op, args, kwargs):
    '''
    This is a generic finalizer. It requires at least one argument to have a length,
    and all arguments that *do* have a length to have the same length.
    '''

    lengths = set(_arg_size(a) for a in args) - { None }
    if len(lengths) != 1:
        raise ClaripyOperationError("Arguments to %s must have equal (and existing) sizes", op)

    kwargs['length'] = lengths.pop()
    return op, args, kwargs

def _finalize_I(claripy, op, args, kwargs):
    '''
    An I object wraps native objects in a Claripy AST. It's used to get the length and name
    of an object (i.e, a StridedInterval or a BV can have a name, and both of those or a BVV
    will have a length.
    '''
    for b in claripy.model_backends:
        try:
            kwargs['length'] = b.size(args[0])
            break
        except BackendError: pass
    else:
        raise ClaripyASTError("no backend can determine size of %s object", type(args[0]))

    for b in claripy.model_backends:
        try:
            name = b.name(args[0])
            if name is not None:
                variables = kwargs.get('variables', set())
                variables.add(name)
                kwargs['variables'] = variables
            break
        except BackendError: pass

    return op, args, kwargs

def _finalize_get_errored(args):
    '''
    This is a helper function. Given a tuple of arguments to an AST operation.
    it returns the union of the backends that errored on any of the arguments.
    '''
    #all_errored = [ ]
    #for a in args:
    #   if isinstance(a, A):
    #       all_errored.append(a._errored)
    #return set.union(set(), *all_errored)
    return set.union(set(), *tuple(a._errored for a in args if isinstance(a, A)))

#pylint:enable=unused-argument

class ASTCacheKey(object): pass

class A(ana.Storable):
    '''
    An A(ST) tracks a tree of operations on arguments. It has the following methods:

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

    __slots__ = [ 'op', 'args', 'length', 'variables', 'symbolic', '_objects', '_collapsible', '_claripy', '_hash', '_simplified', '_cache_key', '_errored', '_rec_id' ]
    _hash_cache = weakref.WeakValueDictionary()

    FULL_SIMPLIFY=1
    LITE_SIMPLIFY=2
    UNSIMPLIFIED=0

    def __new__(cls, claripy, op, args, **kwargs):
        '''
        This is called when you create a new A object, whether directly or through an operation.
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
        '''
        if any(not isinstance(a, (str, int, long, bool, A, BackendObject)) for a in args):
            #import ipdb; ipdb.set_trace()
            raise ClaripyTypeError("arguments %s contain an unknown type to claripy.A" % args)

        a_args = tuple((a.to_claripy() if isinstance(a, BackendObject) else a) for a in args)

        f_op, f_args, f_kwargs = _finalize(claripy, op, a_args, kwargs)
        h = A._calc_hash(claripy, f_op, f_args, f_kwargs)

        #if f_kwargs['length'] is None:
        #   __import__('ipdb').set_trace()


        #print "got hash",h
        #print "... claripy:", hash(claripy.name)
        #print "... op (%r):" % op, hash(op)
        #print "... args (%r):" % (args,), hash(args)

        self = cls._hash_cache.get(h, None)
        if self is None:
            self = super(A, cls).__new__(cls, claripy, f_op, f_args, **f_kwargs)
            self.__a_init__(claripy, f_op, f_args, **f_kwargs)
            self._hash = h
            cls._hash_cache[h] = self
        # else:
        #    if self.args != f_args or self.op != f_op or self.variables != f_kwargs['variables']:
        #        raise Exception("CRAP -- hash collision")

        return self

    def __init__(self, *args, **kwargs):
        pass

    @staticmethod
    def _calc_hash(claripy, op, args, k):
        '''
        Calculates the hash of an AST, given the operation, args, and kwargs.

        @param op: the operation
        @param args: the arguments to the operation
        @param kwargs: a dict including the 'symbolic', 'variables', and 'length' items

        @returns a hash
        '''
        return hash((claripy.name, op, args, k['symbolic'], frozenset(k['variables']), k['length']))

    #pylint:disable=attribute-defined-outside-init
    def __a_init__(self, claripy, op, args, variables=None, symbolic=None, length=None, collapsible=None, simplified=0, errored=None):
        '''
        Initializes an AST. Takes the same arguments as A.__new__()
        '''
        self.op = op
        self.args = args
        self.length = length
        self.variables = frozenset(variables)
        self.symbolic = symbolic

        self._collapsible = True if collapsible is None else collapsible
        self._claripy = claripy
        self._errored = errored if errored is not None else set()

        self._simplified = simplified
        self._cache_key = ASTCacheKey()

        if len(args) == 0:
            raise ClaripyOperationError("AST with no arguments!")

        #if self.op != 'I':
        #   for a in args:
        #       if not isinstance(a, A) and type(a) not in (int, long, bool, str, unicode):
        #           import ipdb; ipdb.set_trace()
        #           l.warning(ClaripyOperationError("Un-wrapped native object of type %s!" % type(a)))
    #pylint:enable=attribute-defined-outside-init

    def make_uuid(self): #pylint:disable=arguments-differ
        '''
        This overrides the default ANA uuid with the hash of the AST. UUID is slow,
        and we'll soon replace it from ANA itself, and this will go away.

        @returns a string representation of the AST hash.
        '''
        return str(self._hash)

    @property
    def uuid(self):
        '''
        I honestly don't know why this is here. (TODO)
        '''
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
        return self.op, self.args, self.length, self.variables, self.symbolic, self._claripy.name, self._hash
    def _ana_setstate(self, state):
        '''
        Support for ANA deserialization.
        '''
        op, args, length, variables, symbolic, clrp, h = state
        A.__a_init__(self, Claripies[clrp], op, args, length=length, variables=variables, symbolic=symbolic)
        self._hash = h
        A._hash_cache[h] = self

    #
    # Collapsing and simplification
    #

    #def _models_for(self, backend):
    #   for a in self.args:
    #       backend.convert_expr(a)
    #       else:
    #           yield backend.convert(a)

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

        if types.count(A) != 0 and not all((a._collapsible for a in raw_args if isinstance(a, A))):
                #l.debug("... not collapsing for op %s because ASTs are present.", self.op)
                return False

        if self.op in not_invertible:
            #l.debug("... collapsing the AST for operation %s because it's not invertible", self.op)
            return True

        constants = sum((types.count(t) for t in (int, long, bool, str, BVV)))
        if constants == len(raw_args):
            #l.debug("... collapsing the AST for operation %s because it's full of constants", self.op)
            return True

        if len([ a for a in raw_args if isinstance(a, StridedInterval) and a.is_integer()]) > 1:
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
            if not isinstance(r, A):
                return I(self._claripy, r, length=self.length, variables=self.variables, symbolic=self.symbolic)
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
        if self.op == 'Reverse' and isinstance(self.args[0], A) and self.args[0].op == 'Reverse':
            return self.args[0].args[0]

        if self.op in reverse_distributable and all((isinstance(a, A) for a in self.args)) and set((a.op for a in self.args)) == { 'Reverse' }:
            inner_a = A(self._claripy, self.op, tuple(a.args[0] for a in self.args)).simplified
            o = A(self._claripy, 'Reverse', (inner_a,), collapsible=True).simplified
            o._simplified = A.LITE_SIMPLIFY
            return o

        return self

    @property
    def reduced(self):
        '''
        A simplified, collapsed version of the AST.
        '''
        a = self.simplified
        if isinstance(a, A):
            return a.collapsed
        else:
            return a

    #
    # Size functions
    #

    def size(self):
        '''
        Returns the length of the AST.
        '''
        return self.length
    __len__ = size

    #
    # Functionality for resolving to model objects
    #

    def arg_models(self):
        '''
        Helper function to return the model (i.e., non-AST) objects of the arguments.
        '''
        return [ (a.model if isinstance(a, A) else a) for a in self.args ]

    def resolved(self, result=None):
        '''
        Returns a model object (i.e., an object that is the result of all the operations
        in the AST), if there is a backend that can handle this AST. Otherwise, return
        itself.

        @arg result: a Result object, for resolving symbolic variables using the
                     concrete backend.
        '''
        for b in self._claripy.model_backends:
            try: return self.resolved_with(b, result=result)
            except BackendError: self._errored.add(b)
        l.debug("all model backends failed for op %s", self.op)
        return self

    @property
    def model(self):
        '''
        The model object (the result of the operation represented by this AST).
        '''
        return self.resolved()

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

    def __repr__(self):
        if not isinstance(self.model, A):
            return "<A %s>" % self.model
        else:
            try:
                return "<A %s %r>" % (self.op, self.args)
            except RuntimeError:
                e_type, value, traceback = sys.exc_info()
                raise ClaripyRecursionError, ("Recursion limit reached during display. I sorry.", e_type, value), traceback

    @property
    def depth(self):
        '''
        The depth of this AST. For example, an AST representing (a+(b+c)) would have
        a depth of 2.
        '''
        ast_args = [ a for a in self.args if isinstance(a, A) ]
        return 1 + (max(a.depth for a in ast_args) if len(ast_args) > 0 else 1)

    @property
    def recursive_children_asts(self):
        for a in self.args:
            if isinstance(a, A):
                yield a
                for b in a.recursive_children_asts:
                    yield b

    def dbg_is_looped(self):
        r = False

        self._rec_id = True #pylint:disable=attribute-defined-outside-init
        for a in self.recursive_children_asts:
            if hasattr(a, '_rec_id') and a._rec_id:
                return True
            else:
                r |= any(a.dbg_is_looped() for a in self.args if isinstance(a, A))
                if r: return True

        delattr(self, '_rec_id')
        return r

    #
    # Various AST modifications (replacements)
    #

    def _do_op(self, op, *args, **kwargs):
        '''
        Returns an AST representing the operation op, with arguments args and kwargs.

        This is a helper function called by the various operation handlers on a
        Claripy object as well as the overloaded operators. For example, the following
        two lines are equivalent:

            c = a + b
            d = a._do_op('__add__', [b])
            assert c is d
        '''
        return A(self._claripy, op, (self,)+args, **kwargs).reduced

    def _replace(self, old, new):
        '''
        A helper for replace().
        '''
        if hash(self) == hash(old):
            return new, True

        new_args = [ ]
        replaced = False

        for a in self.args:
            if isinstance(a, A):
                new_a, a_replaced = a._replace(old, new)
            else:
                new_a, a_replaced = a, False

            new_args.append(new_a)
            replaced |= a_replaced

        if replaced:
            return A(self._claripy, self.op, tuple(new_args)).reduced, True
        else:
            return self, False

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

    # we don't support iterating over A objects
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

    def chop(self, bits=1):
        '''
        Chops an AST into ASTs of size 'bits'. Obviously, the length of the AST must be
        a multiple of bits.
        '''
        s = len(self)
        if s % bits != 0:
            raise ValueError("expression length (%d) should be a multiple of 'bits' (%d)" % (len(self), bits))
        elif s == bits:
            return [ self ]
        else:
            return list(reversed([ self[(n+1)*bits - 1:n*bits] for n in range(0, s / bits) ]))

    @property
    def reversed(self):
        '''
        The reversed AST.
        '''
        return self._do_op('Reverse', collapsible=False)

    def __getitem__(self, rng):
        '''
        Extracts bits from the AST. ASTs are indexed weirdly. For a 32-bit AST:

            a[31] is the *LEFT* most bit, so it'd be the 0 in

                01111111111111111111111111111111

            a[0] is the *RIGHT* most bit, so it'd be the 0 in

                11111111111111111111111111111110

            a[31:30] are the two leftmost bits, so they'd be the 0s in:

                00111111111111111111111111111111

            a[1:0] are the two rightmost bits, so they'd be the 0s in:

                11111111111111111111111111111100

        @returns the new AST.
        '''
        if type(rng) is slice:
            return self._claripy.Extract(int(rng.start), int(rng.stop), self)
        else:
            return self._claripy.Extract(int(rng), int(rng), self)

    def zero_extend(self, n):
        '''
        Zero-extends the AST by n bits. So:

            a = BVV(0b1111, 4)
            b = a.zero_extend(4)
            b is BVV(0b00001111)
        '''
        return self._claripy.ZeroExt(n, self)

    def sign_extend(self, n):
        '''
        Sign-extends the AST by n bits. So:

            a = BVV(0b1111, 4)
            b = a.sign_extend(4)
            b is BVV(0b11111111)
        '''
        return self._claripy.SignExt(n, self)

    def concat(self, *args):
        '''
        Concatenates this AST with the ASTs provided.
        '''
        return self._claripy.Concat(self, *args)

    def identical(self, o):
        '''
        Returns True if 'o' can be easily determined to be identical to this AST.
        Otherwise, return False. Note that the AST *might* still be identical (i.e.,
        if it were simplified via Z3), but it's hard to quickly tell that.
        '''
        return self._claripy.is_identical(self, o)

    def replace(self, old, new):
        '''
        Returns an AST with all instances of the AST 'old' replaced with AST 'new'
        '''
        if not isinstance(old, A) or not isinstance(new, A):
            raise ClaripyOperationError('replacements must be AST nodes')
        if old.size() != new.size():
            raise ClaripyOperationError('replacements must have matching sizes')
        return self._replace(old, new)[0]

class I(A):
    '''
    This is an 'identity' AST -- it acts as a wrapper around model objects.

    All methods have the same functionality as their corresponding methods on the A class.
    '''

    def __new__(cls, claripy, model, **kwargs):
        return A.__new__(cls, claripy, 'I', (model,), **kwargs)

    #def __init__(self, claripy, model, **kwargs):
    #   A.__init__(self, claripy, 'I', (model,), **kwargs)

    def resolved(self, result=None): return self.args[0]
    def resolved_with(self, b, result=None): return b.convert(self.args[0])
    @property
    def depth(self): return 0
    def split(self, split_on): return self

from .errors import BackendError, ClaripyOperationError, ClaripyRecursionError, ClaripyTypeError, ClaripyASTError
from .operations import length_none_operations, length_same_operations, reverse_distributable, not_invertible
from .bv import BVV
from .vsa import StridedInterval
from . import Claripies
from .backend import BackendObject


#
# Overload the operators
#

def e_operator(cls, op_name):
    '''
    Overloads operator op_name on class cls. Used to overload all the operators on the A class.
    '''
    def wrapper(self, *args):
        return self._do_op(op_name, *args)
    wrapper.__name__ = op_name
    setattr(cls, op_name, wrapper)

def make_methods():
    '''
    Overloads all operators on the A class.
    '''
    for name in expression_operations:
        e_operator(A, name)

from .operations import expression_operations
make_methods()
