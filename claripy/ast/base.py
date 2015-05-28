import sys
import weakref
import hashlib
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
        variables = frozenset.union(frozenset(), *(a.variables for a in args if isinstance(a, Base)))
    kwargs['variables'] = variables

    symbolic = kwargs.get('symbolic', None)
    if symbolic is None:
        symbolic = any((a.symbolic for a in args if isinstance(a, Base)))
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
        o,a,k = op, args, kwargs
#        raise ClaripyOperationError("no Base._finalize_* function found for %s" % op)

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
    if isinstance(o, Base): return o.length
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
    args = _typechecker(op, args, ('I', 'I', Base))
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
    an Base objects.
    '''
    args = _typechecker(op, args, ('I', Base))
    length = _arg_size(args[1])
    if length is None:
        raise ClaripyOperationError("extending an object without a length")

    kwargs['length'] = length + args[0]
    return op, args, kwargs

_finalize_SignExt = _finalize_ZeroExt

def _finalize_reversed(claripy, op, args, kwargs):
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
                variables = kwargs.get('variables', frozenset())
                variables = variables.union(frozenset([name]))
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
    #   if isinstance(a, Base):
    #       all_errored.append(a._errored)
    #return set.union(set(), *all_errored)
    return set.union(set(), *(a._errored for a in args if isinstance(a, Base)))

#pylint:enable=unused-argument

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

    __slots__ = [ 'op', 'args', 'variables', 'symbolic', '_objects', '_collapsible', '_claripy', '_hash', '_simplified', '_cache_key', '_errored', 'eager' ]
    _hash_cache = weakref.WeakValueDictionary()

    FULL_SIMPLIFY=1
    LITE_SIMPLIFY=2
    UNSIMPLIFIED=0

    def __new__(cls, claripy, op, args, **kwargs):
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

        a_args = tuple((a.to_claripy() if isinstance(a, BackendObject) else a) for a in args)

        f_op, f_args, f_kwargs = _finalize(claripy, op, a_args, kwargs)

        h = Base._calc_hash(claripy, f_op, f_args, f_kwargs)

        self = cls._hash_cache.get(h, None)
        if self is None:
            self = super(Base, cls).__new__(cls, claripy, f_op, f_args, **f_kwargs)
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
        to_hash = claripy.name + ' ' + op + ' ' + ','.join(str(hash(a)) for a in args) + ' ' + \
                  str(k['symbolic']) + ' ' + str(hash(frozenset(k['variables']))) + ' ' + str(k.get('length', None))
        hd = hashlib.md5(to_hash).hexdigest()

        return int(hd[:16], 16) # 64 bits

    #pylint:disable=attribute-defined-outside-init
    def __a_init__(self, claripy, op, args, variables=None, symbolic=None, length=None, collapsible=None, simplified=0, errored=None, eager=False):
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
        self._claripy = claripy
        self._errored = errored if errored is not None else set()

        self._simplified = simplified
        self._cache_key = ASTCacheKey()

        if self.op != 'I' and all(_is_eager(a) for a in self.args):
            model = self.model
            if model is not self:
                self.op = 'I'
                self.args = (model,)
                self.eager = True

        if len(args) == 0:
            raise ClaripyOperationError("AST with no arguments!")

        #if self.op != 'I':
        #   for a in args:
        #       if not isinstance(a, Base) and type(a) not in (int, long, bool, str, unicode):
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
        Base.__a_init__(self, Claripies[clrp], op, args, length=length, variables=variables, symbolic=symbolic)
        self._hash = h
        Base._hash_cache[h] = self

    #
    # Collapsing and simplification
    #

    #def _models_for(self, backend):
    #   for a in self.args:
    #       backend.convert_expr(a)
    #       else:
    #           yield backend.convert(a)

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
            if not isinstance(r, Base):
                return self._wrap(r)
            else:
                return r
        else:
            return self

    def _wrap(self, r):
        if isinstance(r, (BVV, StridedInterval)):
            return BVI(self._claripy, r, length=r.bits, variables=self.variables, symbolic=self.symbolic)
        elif isinstance(r, bool):
            return BoolI(self._claripy, r, variables=self.variables, symbolic=self.symbolic)
        else:
            raise ClaripyTypeError("unrecognized type to wrap {}".format(type(r)))

    def _simplify_If(self):
        if self.args[0].reduced.is_true():
            return self.args[1].reduced

        if self.args[0].reduced.is_false():
            return self.args[2].reduced

        return self

    def _simplify_Reverse(self):
        if self.args[0].op == 'Reverse':
            return self.args[0].args[0]

        if self.args[0].op == 'Concat':
            if all(a.op == 'Extract' for a in self.args[0].args):
                first_ast = self.args[0].args[0].args[2]
                for i, ast in enumerate(self.args[0].args):
                    if not (first_ast.identical(ast.args[2])
                            and ast.args[0] == ((i + 1) * 8 - 1)
                            and ast.args[1] == i * 8):
                        break
                else:
                    upper_bound = self.args[0].args[-1].args[0]
                    if first_ast.length == upper_bound + 1:
                        return first_ast
                    else:
                        return first_ast[upper_bound:0]

        return self

    def _simplify_Extract(self):
        high, low = self.args[:2]

        val = self.args[2]
        if val.op == 'ZeroExt':
            val = self._claripy.Concat(self._claripy.BVV(0, val.args[0]), val.args[1])

        if val.op == 'Concat':
            pos = val.length
            high_i, low_i, low_loc = None, None, None
            for i, v in enumerate(val.args):
                if high in xrange(pos - v.length, pos):
                    high_i = i
                if low in xrange(pos - v.length, pos):
                    low_i = i
                    low_loc = low - (pos - v.length)
                pos -= v.length
            if high_i is None or low_i is None:
                raise Exception("wat")

            used = val.args[high_i:low_i+1]
            if len(used) == 1:
                self = used[0]
            else:
                self = self._claripy.Concat(*used)

            new_high = low_loc + high - low
            if new_high == self.length - 1 and low_loc == 0:
                return self
            else:
                self = self[new_high:low_loc]

        if self.op == 'Extract' and self.args[2].op == 'Extract':
            high, low = self.args[:2]
            _, inner_low = self.args[2].args[:2]
            new_low = inner_low + low
            new_high = new_low + (high - low)
            self = (self.args[2].args[2])[new_high:new_low]

        return self

    def _simplify_Not(self):
        if self.args[0].op == '__eq__':
            return self.args[0].args[0] != self.args[0].args[1]
        elif self.args[0].op == '__ne__':
            return self.args[0].args[0] == self.args[0].args[1]
        else:
            return self

    @property
    def simplified(self):
        '''
        A lightly simplified version of the AST (simplify level 1). This basically
        just cancels out two Reverse operations, if they are present. Later on, it will hopefully
        do more.
        '''
        # note: should cover __radd__ etc. somehow
        if hasattr(self, '_simplify_' + self.op):
            self = getattr(self, '_simplify_' + self.op)()

        if self.op in reverse_distributable and all((isinstance(a, Base) for a in self.args)) and set((a.op for a in self.args)) == { 'Reverse' }:
            inner_a = self.make_like(self._claripy, self.op, tuple(a.args[0] for a in self.args)).simplified
            o = self.make_like(self._claripy, 'Reverse', (inner_a,), collapsible=True).simplified
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

    def dbg_repr(self):
        try:
            return "<%s %s (%s)>" % (type(self).__name__, self.op, ', '.join(a.dbg_repr() if hasattr(a, 'dbg_repr') else repr(a) for a in self.args))
        except RuntimeError:
            e_type, value, traceback = sys.exc_info()
            raise ClaripyRecursionError, ("Recursion limit reached during display. I sorry.", e_type, value), traceback

    def _type_name(self):
        return self.__class__.__name__

    def __repr__(self, inner=False, explicit_length=False):
        self = self.reduced

        if not isinstance(self.model, Base):
            if inner:
                if isinstance(self.model, BVV):
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
        raise Exception("_do_op is dead! (or at least should be...)")
        return type(self)(self._claripy, op, (self,)+args, **kwargs).reduced

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
                r = self.make_like(self._claripy, self.op, tuple(new_args)).reduced
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
        return self._claripy.is_identical(self, o)

    def replace(self, old, new):
        '''
        Returns an AST with all instances of the AST 'old' replaced with AST 'new'
        '''
        if not isinstance(old, Base) or not isinstance(new, Base):
            raise ClaripyOperationError('replacements must be AST nodes')
        if old.size() != new.size():
            raise ClaripyOperationError('replacements must have matching sizes')
        return self._replace(old, new)

from ..errors import BackendError, ClaripyOperationError, ClaripyRecursionError, ClaripyTypeError, ClaripyASTError
from .. import operations
from ..operations import length_none_operations, length_same_operations, reverse_distributable, not_invertible
from ..bv import BVV
from ..fp import RM, FSort
from ..vsa import StridedInterval
from .. import Claripies
from ..backend import BackendObject
from .bv import BVI
from .bool import BoolI
