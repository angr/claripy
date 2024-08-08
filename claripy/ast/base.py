from __future__ import annotations

import itertools
import logging
import math
import struct
from collections import OrderedDict, deque
from enum import IntEnum
from itertools import chain
from typing import TYPE_CHECKING, Any, Generic, NoReturn, TypeVar, Union, cast
from weakref import WeakValueDictionary

from typing_extensions import Self

from claripy import operations, simplifications
from claripy.backend_manager import backends
from claripy.errors import BackendError, ClaripyOperationError, ClaripyReplacementError

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Iterator

    from claripy import Backend
    from claripy.annotation import Annotation

try:
    import _pickle as pickle
except ImportError:
    import pickle

try:
    # Python's build-in MD5 is about 2x faster than hashlib.md5 on short bytestrings
    import _md5 as md5
except ImportError:
    import hashlib as md5

l = logging.getLogger("claripy.ast")

md5_unpacker = struct.Struct("2Q")
from_iterable = chain.from_iterable

# pylint:enable=unused-argument

ArgType = Union["Base", bool, int, float, str, tuple["ArgType"], None]
# TODO: HashType should be int, but it isn't always int
HashType = int | bytes | tuple[Any, ...]

T = TypeVar("T", bound="Base")


class ASTCacheKey(Generic[T]):
    """ASTCacheKey is a wrapper around an AST that is used as a key in caches."""

    def __init__(self, a: T):
        self.ast: T = a

    def __hash__(self):
        return hash(self.ast)

    def __eq__(self, other):
        return type(self) is type(other) and self.ast._hash == other.ast._hash

    def __repr__(self):
        return f"<Key {self.ast._type_name()} {self.ast.__repr__(inner=True)}>"


class SimplificationLevel(IntEnum):
    """
    Simplification levels for ASTs.
    """

    UNSIMPLIFIED = 0
    LITE_SIMPLIFY = 1
    FULL_SIMPLIFY = 2


class ReprLevel(IntEnum):
    """
    Representation levels for ASTs.
    """

    LITE_REPR = 0
    MID_REPR = 1
    FULL_REPR = 2


#
# AST variable naming
#

var_counter = itertools.count()
_unique_names = True


def _make_name(name: str, size: int, explicit_name: bool = False, prefix: str = "") -> str:
    if _unique_names and not explicit_name:
        return "%s%s_%d_%d" % (prefix, name, next(var_counter), size)
    else:
        return name


def _d(h, cls, state):
    """
    This function is the deserializer for ASTs.
    It exists to work around the fact that pickle will (normally) call __new__() with no arguments during
    deserialization. For ASTs, this does not work.
    """
    op, args, length, variables, symbolic, annotations = state
    return cls.__new__(
        cls, op, args, length=length, variables=variables, symbolic=symbolic, annotations=annotations, hash=h
    )


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

    # Hashcons
    op: str
    args: tuple[ArgType, ...]
    length: int | None
    variables: frozenset[str]
    symbolic: bool
    annotations: tuple[Annotation, ...]

    # Derived information
    depth: int
    _hash: int | bytes  # TODO: This should be int, but it isn't always int
    _simplified: SimplificationLevel
    _uneliminatable_annotations: frozenset[Annotation]

    # Backend information
    _eager_backends: list[Backend]
    _errored: set[Backend]

    # Caching
    _ast_cache_key: ASTCacheKey[Self]
    _cached_encoded_name: bytes | None

    # Extra information
    _excavated: Base | None
    _burrowed: Base | None
    _uninitialized: bool
    _uc_alloc_depth: int

    __slots__ = [
        "op",
        "args",
        "length",
        "variables",
        "symbolic",
        "annotations",
        "depth",
        "_hash",
        "_simplified",
        "_uneliminatable_annotations",
        "_relocatable_annotations",
        "_eager_backends",
        "_errored",
        "_cache_key",
        "_cached_encoded_name",
        "_excavated",
        "_burrowed",
        "_uninitialized",
        "_uc_alloc_depth",
        "__weakref__",
    ]

    _hash_cache: WeakValueDictionary[HashType, Base] = WeakValueDictionary()
    _leaf_cache: WeakValueDictionary[HashType, Base] = WeakValueDictionary()

    def __new__(  # pylint:disable=redefined-builtin
        cls: type[Base],
        op: str,
        args: Iterable[ArgType],
        add_variables: Iterable[str] | None = None,
        hash: int | None = None,
        symbolic: bool | None = None,
        variables: set[str] | None = None,
        errored: set[Backend] | None = None,
        eager_backends: set[Backend] | None = None,
        uninitialized: bool | None = None,
        uc_alloc_depth: int | None = None,
        annotations: tuple[Annotation, ...] = (),
        skip_child_annotations: bool = False,
        length: int | None = None,
        encoded_name: bytes | None = None,
    ):
        """
        This is called when you create a new Base object, whether directly or through an operation.
        It finalizes the arguments (see the _finalize function, above) and then computes
        a hash. If an AST of this hash already exists, it returns that AST. Otherwise,
        it creates, initializes, and returns the AST.

        :param op:                  The AST operation ('__add__', 'Or', etc)
        :param args:                The arguments to the AST operation (i.e., the objects to add)
        :param variables:           The symbolic variables present in the AST (default: empty set)
        :param symbolic:            A flag saying whether or not the AST is symbolic (default: False)
        :param length:              An integer specifying the bit length of this AST (default: None)
        :param simplified:          A measure of how simplified this AST is. 0 means unsimplified,
                                        1 means fast-simplified (basically, just undoing the Reverse
                                        op), and 2 means simplified through z3.
        :param errored:             A set of backends that are known to be unable to handle this AST.
        :param eager_backends:      A list of backends with which to attempt eager evaluation
        :param annotations:         A frozenset of annotations applied onto this AST.
        """

        # if any(isinstance(a, BackendObject) for a in args):
        #   raise Exception('asdf')

        a_args = args if type(args) is tuple else tuple(args)

        # initialize the following properties: symbolic, variables and errored
        need_symbolic = symbolic is None
        need_variables = variables is None
        need_errored = errored is None
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
                if not isinstance(a, Base):
                    continue
                if need_symbolic and not symbolic_flag:
                    symbolic_flag |= a.symbolic
                if need_variables:
                    variables_set |= a.variables
                if need_errored:
                    errored_set |= a._errored
                if args_have_annotations is not True:
                    args_have_annotations = args_have_annotations or bool(a.annotations)
                arg_max_depth = max(arg_max_depth, a.depth)

            if need_symbolic:
                symbolic = symbolic_flag
            if need_variables:
                variables = frozenset(variables_set)
            if need_errored:
                errored = errored_set

        if not isinstance(variables, frozenset):
            variables = frozenset(variables)

        if add_variables:
            variables = variables | add_variables

        if eager_backends is None:
            eager_backends = list(backends._eager_backends)

        if not symbolic and op not in operations.leaf_operations:
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
            eager_backends = None

        # process annotations
        if not annotations and not args_have_annotations:
            uneliminatable_annotations = frozenset()
            relocatable_annotations = frozenset()
        else:
            ast_args = tuple(a for a in a_args if isinstance(a, Base))
            uneliminatable_annotations = frozenset(
                chain(
                    (
                        from_iterable(a._uneliminatable_annotations for a in ast_args)
                        if not skip_child_annotations
                        else ()
                    ),
                    tuple(a for a in annotations if not a.eliminatable and not a.relocatable),
                )
            )

            relocatable_annotations = tuple(
                OrderedDict(
                    (e, True)
                    for e in tuple(
                        chain(
                            (
                                from_iterable(a._relocatable_annotations for a in ast_args)
                                if not skip_child_annotations
                                else ()
                            ),
                            tuple(a for a in annotations if not a.eliminatable and a.relocatable),
                        )
                    )
                ).keys()
            )

            annotations = tuple(
                chain(
                    (from_iterable(a._relocatable_annotations for a in ast_args) if not skip_child_annotations else ()),
                    tuple(a for a in annotations),
                )
            )

        cache = cls._hash_cache
        if hash is not None:
            h = hash
        elif op in {"BVS", "BVV", "BoolS", "BoolV", "FPS", "FPV"} and not annotations:
            if op == "FPV" and a_args[0] == 0.0 and math.copysign(1, a_args[0]) < 0:
                # Python does not distinguish between +0.0 and -0.0 so we add sign to tuple to distinguish
                h = (op, length, ("-", *a_args))
            elif op == "FPV" and math.isnan(a_args[0]):
                # cannot compare nans
                h = (op, length, ("nan",) + a_args[1:])
            else:
                h = (op, length, a_args)

            cache = cls._leaf_cache
        else:
            h = (
                Base._calc_hash(
                    op,
                    a_args,
                    variables,
                    symbolic,
                    annotations,
                    length=length,
                )
                if hash is None
                else hash
            )
        self = cache.get(h, None)
        if self is None:
            self = super().__new__(cls)
            depth = arg_max_depth + 1
            self.__a_init__(
                op,
                a_args,
                variables=variables,
                symbolic=symbolic,
                length=length,
                errored=errored,
                eager_backends=eager_backends,
                uninitialized=uninitialized,
                uc_alloc_depth=uc_alloc_depth,
                annotations=annotations,
                encoded_name=encoded_name,
                depth=depth,
                uneliminatable_annotations=uneliminatable_annotations,
                relocatable_annotations=relocatable_annotations,
            )
            self._hash = h
            cache[h] = self
        # else:
        #   if self.args != a_args or self.op != op or self.variables != kwargs['variables']:
        #       raise Exception("CRAP -- hash collision")

        return self

    def __reduce__(self):
        # HASHCONS: these attributes key the cache
        # BEFORE CHANGING THIS, SEE ALL OTHER INSTANCES OF "HASHCONS" IN THIS FILE
        return _d, (
            self._hash,
            self.__class__,
            (self.op, self.args, self.length, self.variables, self.symbolic, self.annotations),
        )

    def __init__(self, *args, **kwargs):
        pass

    @staticmethod
    def _calc_hash(
        op: str,
        args: tuple[Base, ...],
        variables: set[str],
        symbolic: bool,
        annotations: set[Annotation],
        length: int | None = None,
    ) -> bytes:
        """
        Calculates the hash of an AST, given the operation, args, and kwargs.

        :param op:                  The operation.
        :param args:                The arguments to the operation.
        :param keywords:            A dict including the 'symbolic', 'variables', and 'length' items.
        :returns:                   a hash.

        We do it using md5 to avoid hash collisions.
        (hash(-1) == hash(-2), for example)
        """
        args_tup = tuple(a if type(a) in (int, float) else getattr(a, "_hash", hash(a)) for a in args)
        # HASHCONS: these attributes key the cache
        # BEFORE CHANGING THIS, SEE ALL OTHER INSTANCES OF "HASHCONS" IN THIS FILE

        to_hash = Base._ast_serialize(
            op,
            args_tup,
            length,
            variables,
            symbolic,
            annotations,
        )
        if to_hash is None:
            # fall back to pickle.dumps
            to_hash = (
                op,
                args_tup,
                str(length),
                hash(variables),
                symbolic,
                hash(annotations),
            )
            to_hash = pickle.dumps(to_hash, -1)

        # Why do we use md5 when it's broken? Because speed is more important
        # than cryptographic integrity here. Then again, look at all those
        # allocations we're doing here... fast python is painful.
        hd = md5.md5(to_hash).digest()
        return md5_unpacker.unpack(hd)[0]  # 64 bits

    @staticmethod
    def _arg_serialize(arg: ArgType) -> bytes | None:
        if arg is None:
            return b"\x0f"
        elif arg is True:
            return b"\x1f"
        elif arg is False:
            return b"\x2e"
        elif isinstance(arg, int):
            if arg < 0:
                if arg >= -0x7FFF:
                    return b"-" + struct.pack("<h", arg)
                elif arg >= -0x7FFF_FFFF:
                    return b"-" + struct.pack("<i", arg)
                elif arg >= -0x7FFF_FFFF_FFFF_FFFF:
                    return b"-" + struct.pack("<q", arg)
                return None
            else:
                if arg <= 0xFFFF:
                    return struct.pack("<H", arg)
                elif arg <= 0xFFFF_FFFF:
                    return struct.pack("<I", arg)
                elif arg <= 0xFFFF_FFFF_FFFF_FFFF:
                    return struct.pack("<Q", arg)
                return None
        elif isinstance(arg, str):
            return arg.encode()
        elif isinstance(arg, float):
            return struct.pack("f", arg)
        elif isinstance(arg, tuple):
            arr = []
            for elem in arg:
                b = Base._arg_serialize(elem)
                if b is None:
                    return None
                arr.append(b)
            return b"".join(arr)

        return None

    @staticmethod
    def _ast_serialize(
        op: str,
        args_tup: tuple[ArgType, ...],
        length: int,
        variables: set[str],
        symbolic: bool,
        annotations: set[Annotation],
    ) -> bytes | None:
        """
        Serialize the AST and get a bytestring for hashing.

        :param op:          The operator.
        :param args_tup:    A tuple of arguments.
        :param keywords:    A dict of keywords.
        :return:            The serialized bytestring.
        """

        serialized_args = Base._arg_serialize(args_tup)
        if serialized_args is None:
            return None

        length = Base._arg_serialize(length)
        variables = struct.pack("<Q", hash(variables) & 0xFFFF_FFFF_FFFF_FFFF)
        symbolic = b"\x01" if symbolic else b"\x00"
        annotations = struct.pack("<Q", hash(annotations) & 0xFFFF_FFFF_FFFF_FFFF)

        return op.encode() + serialized_args + length + variables + symbolic + annotations

    # pylint:disable=attribute-defined-outside-init
    def __a_init__(
        self,
        op: str,
        args: tuple[ArgType, ...],
        variables: Iterable[str] | None = None,
        symbolic: bool | None = None,
        length: int | None = None,
        simplified: SimplificationLevel = SimplificationLevel.UNSIMPLIFIED,
        errored: set[Backend] | None = None,
        eager_backends: set[Backend] | None = None,
        uninitialized: bool | None = None,
        uc_alloc_depth: int | None = None,
        annotations: Iterable[Annotation] | None = None,
        encoded_name: bytes | None = None,
        depth: int | None = None,
        uneliminatable_annotations: frozenset[Annotation] | None = None,
        relocatable_annotations: frozenset[Annotation] | None = None,
    ) -> None:
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
        self.annotations: tuple[Annotation] = annotations
        self._uneliminatable_annotations = uneliminatable_annotations
        self._relocatable_annotations = relocatable_annotations

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

        if len(self.args) == 0:
            raise ClaripyOperationError("AST with no arguments!")

    # pylint:enable=attribute-defined-outside-init

    def __hash__(self) -> int:
        res = self._hash
        if not isinstance(self._hash, int):
            res = hash(self._hash)
        return res

    @property
    def cache_key(self: Self) -> ASTCacheKey[Self]:
        """
        A key that refers to this AST - this value is appropriate for usage as a key in dictionaries.
        """
        return self._cache_key

    @property
    def _encoded_name(self) -> bytes:
        if self._cached_encoded_name is None:
            self._cached_encoded_name = self.args[0].encode()
        return self._cached_encoded_name

    #
    # Collapsing and simplification
    #

    def make_like(
        self,
        op: str,
        args: Iterable[ArgType],
        simplify: bool = False,
        annotations: set[Annotation] | None = None,
        variables: set[str] | None = None,
        symbolic: bool | None = None,
        uninitialized: bool | None = None,
        skip_child_annotations: bool = False,
        length: int | None = None,
    ) -> Self:
        # Try to simplify the expression again
        simplified = simplifications.simpleton.simplify(op, args) if simplify else None
        if simplified is not None:
            op = simplified.op
        if (  # fast path
            simplified is None
            and annotations
            and variables is None
            and symbolic is None
            and uninitialized is None
            and skip_child_annotations
            and length is not None
        ):
            uneliminatable_annotations = frozenset(
                anno for anno in annotations if not anno.eliminatable and not anno.relocatable
            )
            relocatable_annotations = frozenset(
                anno for anno in annotations if not anno.eliminatable and anno.relocatable
            )

            cache = type(self)._hash_cache
            h = Base._calc_hash(
                op,
                args,
                self.variables,
                self.symbolic,
                annotations,
                length=length,
            )
            cached_ast = cast(T | None, cache.get(h, None))
            if cached_ast is not None:
                return cached_ast

            result: T = super().__new__(type(self))
            result.__a_init__(
                op,
                args,
                depth=self.depth,
                uneliminatable_annotations=uneliminatable_annotations,
                relocatable_annotations=relocatable_annotations,
                variables=self.variables,
                symbolic=self.symbolic,
                annotations=annotations,
                length=length,
                uninitialized=self._uninitialized,
                eager_backends=self._eager_backends,
                uc_alloc_depth=self.uc_alloc_depth,
            )

            result._hash = h
            cache[h] = result

            return result

        all_operations = operations.leaf_operations_symbolic_with_union
        # special case: if self is one of the args, we do not copy annotations over from self since child
        # annotations will be re-processed during AST creation.
        if annotations is None:
            annotations = self.annotations if not args or not any(self is arg for arg in args) else ()
        if variables is None and op in all_operations:
            variables = self.variables
        if uninitialized is None:
            uninitialized = self._uninitialized
        if symbolic is None and op in all_operations:
            symbolic = self.symbolic

        return type(self)(
            op,
            args if simplified is None else simplified.args,
            annotations=annotations,
            variables=variables,
            uninitialized=uninitialized,
            symbolic=symbolic,
            skip_child_annotations=skip_child_annotations,
            length=length,
        )

    def _rename(self, new_name: str) -> Self:
        if self.op not in {"BVS", "BoolS", "FPS"}:
            raise ClaripyOperationError("rename is only supported on leaf nodes")
        new_args = (new_name,) + self.args[1:]
        return self.make_like(self.op, new_args, length=self.length, variables={new_name})

    #
    # Annotations
    #

    def _apply_to_annotations(self, f):
        return self.make_like(self.op, self.args, annotations=f(self.annotations), skip_child_annotations=True)

    def append_annotation(self, a: Annotation) -> Self:
        """
        Appends an annotation to this AST.

        :param a:                   the annotation to append
        :returns:                   a new AST, with the annotation added
        """
        return self._apply_to_annotations(lambda alist: (*alist, a))

    def append_annotations(self, new_tuple: tuple[Annotation, ...]) -> Self:
        """
        Appends several annotations to this AST.

        :param new_tuple:           the tuple of annotations to append
        :returns:                   a new AST, with the annotations added
        """
        return self._apply_to_annotations(lambda alist: alist + new_tuple)

    def annotate(self, *args: Annotation, remove_annotations: Iterable[Annotation] | None = None) -> Self:
        """
        Appends annotations to this AST.

        :param args:                the tuple of annotations to append (variadic positional args)
        :param remove_annotations:  annotations to remove
        :returns:                   a new AST, with the annotations added
        """
        if not remove_annotations:
            return self._apply_to_annotations(lambda alist: alist + args)
        else:
            return self._apply_to_annotations(
                lambda alist: tuple(arg for arg in alist if arg not in remove_annotations) + args
            )

    def insert_annotation(self, a: Annotation) -> Self:
        """
        Inserts an annotation to this AST.

        :param a:                   the annotation to insert
        :returns:                   a new AST, with the annotation added
        """
        return self._apply_to_annotations(lambda alist: (a, *alist))

    def insert_annotations(self, new_tuple: tuple[Annotation, ...]) -> Self:
        """
        Inserts several annotations to this AST.

        :param new_tuple:           the tuple of annotations to insert
        :returns:                   a new AST, with the annotations added
        """
        return self._apply_to_annotations(lambda alist: new_tuple + alist)

    def replace_annotations(self, new_tuple: tuple[Annotation, ...]) -> Self:
        """
        Replaces annotations on this AST.

        :param new_tuple:           the tuple of annotations to replace the old annotations with
        :returns:                   a new AST, with the annotations added
        """
        return self._apply_to_annotations(lambda alist: new_tuple)

    def remove_annotation(self, a: Annotation) -> Self:
        """
        Removes an annotation from this AST.

        :param a:                   the annotation to remove
        :returns:                   a new AST, with the annotation removed
        """
        return self._apply_to_annotations(lambda alist: tuple(oa for oa in alist if oa != a))

    def remove_annotations(self, remove_sequence: Iterable[Annotation]) -> Self:
        """
        Removes several annotations from this AST.

        :param remove_sequence:     a sequence/set of the annotations to remove
        :returns:                   a new AST, with the annotations removed
        """
        return self._apply_to_annotations(lambda alist: tuple(oa for oa in alist if oa not in remove_sequence))

    def clear_annotations(self) -> Self:
        """
        Removes all annotations from this AST.

        :returns:                   a new AST, with all annotations removed
        """
        return self._apply_to_annotations(lambda _: ())

    #
    # Viewing and debugging
    #

    def dbg_repr(self, prefix=None) -> str:  # pylint:disable=unused-argument
        """
        Returns a debug representation of this AST.
        """
        return self.shallow_repr(max_depth=None, details=ReprLevel.FULL_REPR)

    def _type_name(self) -> str:
        return self.__class__.__name__

    def __repr__(self, inner=False, max_depth=None, explicit_length=False):
        return self.shallow_repr(max_depth=max_depth, explicit_length=explicit_length, inner=inner)

    def shallow_repr(
        self,
        max_depth: int = 8,
        explicit_length: bool = False,
        details: ReprLevel = ReprLevel.LITE_REPR,
        inner: bool = False,
        parent_prec: int = 15,
        left: bool = True,
    ) -> str:
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
            return "<...>"

        elif self.op in operations.reversed_ops:
            op = operations.reversed_ops[self.op]
            args = reversed(self.args)
        else:
            op = self.op
            args = self.args

        next_max_depth = max_depth - 1 if max_depth is not None else None
        length = self.length if explicit_length else None
        # if operation is not in op_precedence, assign the "least operation precedence"
        op_prec = operations.op_precedence.get(op, 15)

        args = [
            (
                arg.shallow_repr(next_max_depth, explicit_length, details, True, op_prec, idx == 0)
                if isinstance(arg, Base)
                else arg
            )
            for idx, arg in enumerate(args)
        ]

        prec_diff = parent_prec - op_prec
        inner_infix_use_par = prec_diff < 0 or prec_diff == 0 and not left
        inner_repr = self._op_repr(op, args, inner, length, details, inner_infix_use_par)

        if not inner:
            return f"<{self._type_name()} {inner_repr}>"
        else:
            return inner_repr

    @staticmethod
    def _op_repr(
        op: str,
        args: tuple[ArgType, ...],
        inner: ArgType,
        length: int | None,
        details: ReprLevel,
        inner_infix_use_par: bool,
    ):
        if details < ReprLevel.FULL_REPR:
            if op == "BVS":
                extras = []
                if args[1] is not None:
                    fmt = "%#x" if isinstance(args[1], int) else "%s"
                    extras.append("min=%s" % (fmt % args[1]))
                if args[2] is not None:
                    fmt = "%#x" if isinstance(args[2], int) else "%s"
                    extras.append("max=%s" % (fmt % args[2]))
                if args[3] is not None:
                    fmt = "%#x" if isinstance(args[3], int) else "%s"
                    extras.append("stride=%s" % (fmt % args[3]))
                if args[4] is True:
                    extras.append("UNINITIALIZED")
                return "{}{}".format(args[0], "{{{}}}".format(", ".join(extras)) if extras else "")

            elif op == "BoolV":
                return str(args[0])

            elif op == "BVV":
                if args[0] is None:
                    value = "!"
                elif args[1] < 10:
                    value = format(args[0], "")
                else:
                    value = format(args[0], "#x")
                return value + "#%d" % length if length is not None else value

        if details < ReprLevel.MID_REPR:
            if op == "If":
                value = f"if {args[0]} then {args[1]} else {args[2]}"
                return f"({value})" if inner else value

            elif op == "Not":
                return f"!{args[0]}"

            elif op == "Extract":
                return f"{args[2]}[{args[0]}:{args[1]}]"

            elif op == "ZeroExt":
                value = f"0#{args[0]} .. {args[1]}"
                return f"({value})" if inner else value

            elif op in operations.prefix:
                assert len(args) == 1
                value = f"{operations.prefix[op]}{args[0]}"
                return f"({value})" if inner and inner_infix_use_par else value

            elif op in operations.infix:
                value = f" {operations.infix[op]} ".join(args)
                return f"({value})" if inner and inner_infix_use_par else value

        return "{}({})".format(op, ", ".join(str(arg) for arg in args))

    def children_asts(self) -> Iterator[Base]:
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

    def leaf_asts(self) -> Iterator[Base]:
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

    def dbg_is_looped(self) -> bool:
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

    def swap_args(self, new_args: tuple[ArgType, ...], new_length: int | None = None, **kwargs) -> Self:
        """
        This returns the same AST, with the arguments swapped out for new_args.
        """

        if len(self.args) == len(new_args) and all(a is b for a, b in zip(self.args, new_args)):
            return self

        # symbolic = any(a.symbolic for a in new_args if isinstance(a, Base))
        # variables = frozenset.union(frozenset(), *(a.variables for a in new_args if isinstance(a, Base)))
        length = self.length if new_length is None else new_length
        a = self.make_like(self.op, new_args, length=length, **kwargs)
        # if a.op != self.op or a.symbolic != self.symbolic or a.variables != self.variables:
        #   raise ClaripyOperationError("major bug in swap_args()")
        return a

    #
    # Other helper functions
    #

    def split(self, split_on: Iterable[str]) -> list[ArgType]:
        """
        Splits the AST if its operation is `split_on` (i.e., return all the arguments). Otherwise, return a list with
        just the AST.
        """
        if self.op in split_on:
            return list(self.args)
        else:
            return [self]

    # we don't support iterating over Base objects
    def __iter__(self) -> NoReturn:
        """
        This prevents people from iterating over ASTs.
        """
        raise ClaripyOperationError("Please don't iterate over, or split, AST nodes!")

    def __bool__(self) -> NoReturn:
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
        raise ClaripyOperationError(
            "testing Expressions for truthiness does not do what you want, as these expressions can be symbolic"
        )

    def structurally_match(self, o: Self) -> bool:
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
                if type(arg_a) != type(arg_b):  # noqa: E721
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

    def replace_dict(
        self, replacements, variable_set: set[str] | None = None, leaf_operation: Callable[[Base], Base] | None = None
    ) -> Self:
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

                if ast.cache_key in replacements:
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

            except StopIteration:
                arg_queue.pop()

                if ast_queue:
                    ast = ast_queue.pop()
                    repl = ast

                    args = rep_queue[-len(ast.args) :]
                    del rep_queue[-len(ast.args) :]

                    # Check if replacement occurred.
                    if any((a is not b for a, b in zip(ast.args, args))):
                        repl = ast.make_like(ast.op, tuple(args))
                        replacements[ast.cache_key] = repl

                    rep_queue.append(repl)

        assert len(arg_queue) == 0, "arg_queue is not empty"
        assert len(ast_queue) == 0, "ast_queue is not empty"
        assert len(rep_queue) == 1, ("rep_queue has unexpected length", len(rep_queue))

        return rep_queue.pop()

    def replace(self, old: T, new: T) -> Self:
        """
        Returns this AST but with the AST 'old' replaced with AST 'new' in its subexpressions.
        """
        self._check_replaceability(old, new)
        replacements = {old.cache_key: new}
        return self.replace_dict(replacements, variable_set=old.variables)

    @staticmethod
    def _check_replaceability(old: T, new: T) -> None:
        if not isinstance(old, Base) or not isinstance(new, Base):
            raise ClaripyReplacementError("replacements must be AST nodes")
        if type(old) is not type(new):
            raise ClaripyReplacementError(f"cannot replace type {type(old)} ast with type {type(new)} ast")

    def canonicalize(self, var_map=None, counter=None) -> Self:
        counter = itertools.count() if counter is None else counter
        var_map = {} if var_map is None else var_map

        for v in self.leaf_asts():
            if v.cache_key not in var_map and v.op in {"BVS", "BoolS", "FPS"}:
                new_name = "canonical_%d" % next(counter)
                var_map[v.cache_key] = v._rename(new_name)

        return var_map, counter, self.replace_dict(var_map)

    #
    # This code handles burrowing ITEs deeper into the ast and excavating
    # them to shallower levels.
    #

    def _burrow_ite(self):
        if self.op != "If":
            # print("i'm not an if")
            return self.swap_args([(a.ite_burrowed if isinstance(a, Base) else a) for a in self.args])

        if not all(isinstance(a, Base) for a in self.args):
            # print("not all my args are bases")
            return self

        old_true = self.args[1]
        old_false = self.args[2]

        if old_true.op != old_false.op or len(old_true.args) != len(old_false.args):
            return self

        if old_true.op == "If":
            # let's no go into this right now
            return self

        if any(a.op in operations.leaf_operations for a in self.args):
            # burrowing through these is pretty funny
            return self

        matches = [old_true.args[i] is old_false.args[i] for i in range(len(old_true.args))]
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

                    args = arg_queue[-len(op.args) :]
                    del arg_queue[-len(op.args) :]

                    ite_args = [isinstance(a, Base) and a.op == "If" for a in args]

                    if op.op == "If":
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
                            if not isinstance(a, Base) or a.op != "If":
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
                            excavated = If(
                                cond,
                                op.swap_args(new_true_args, simplify=True),
                                op.swap_args(new_false_args, simplify=True),
                            )

                    # continue
                    arg_queue.append(excavated)

        assert len(op_queue) == 0, "op_queue is not empty"
        assert len(ast_queue) == 0, "ast_queue is not empty"
        assert len(arg_queue) == 1, ("arg_queue has unexpected length", len(arg_queue))

        return arg_queue.pop()

    @property
    def ite_burrowed(self: T) -> T:
        """
        Returns an equivalent AST that "burrows" the ITE expressions as deep as possible into the ast, for simpler
        printing.
        """
        if self._burrowed is None:
            self._burrowed = self._burrow_ite()  # pylint:disable=attribute-defined-outside-init
            self._burrowed._burrowed = self._burrowed  # pylint:disable=attribute-defined-outside-init
        return self._burrowed

    @property
    def ite_excavated(self: T) -> T:
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
            if b in self._errored:
                continue

            try:
                return getattr(b, what)(self)
            except BackendError:
                pass
        return None

    @property
    def concrete_value(self):
        try:
            return backends.concrete.convert(self).value
        except BackendError:
            return self

    @property
    def singlevalued(self) -> bool:
        return self._first_backend("singlevalued")

    @property
    def multivalued(self) -> bool:
        return self._first_backend("multivalued")

    @property
    def cardinality(self) -> int:
        return self._first_backend("cardinality")

    @property
    def concrete(self) -> bool:
        # fast path
        if self.op in {"BVV", "BoolV", "FPV"}:
            return True
        if self.op in {"BVS", "BoolS", "FPS"}:
            return False
        if self.variables:
            return False
        return backends.concrete.handles(self)

    @property
    def uninitialized(self) -> bool:
        """
        Whether this AST comes from an uninitialized dereference or not. It's only used in under-constrained symbolic
        execution mode.

        :returns:                   True/False/None (unspecified).
        """

        # TODO: It should definitely be moved to the proposed Annotation backend.

        return self._uninitialized

    @property
    def uc_alloc_depth(self) -> int:
        """
        The depth of allocation by lazy-initialization. It's only used in under-constrained symbolic execution mode.

        :returns:                   An integer indicating the allocation depth, or None if it's not from
                                    lazy-initialization.
        """
        # TODO: It should definitely be moved to the proposed Annotation backend.

        return self._uc_alloc_depth

    def to_claripy(self: T) -> T:
        """
        Returns itself. Provides compatibility with other classes (such as SimActionObject) which provide a similar
        method to unwrap to an AST.
        """
        return self


def simplify(e: T) -> T:
    if isinstance(e, Base) and e.op in operations.leaf_operations:
        return e

    s = e._first_backend("simplify")
    if s is None:
        l.debug("Unable to simplify expression")
        return e
    else:
        # Copy some parameters (that should really go to the Annotation backend)
        s._uninitialized = e.uninitialized
        s._uc_alloc_depth = e._uc_alloc_depth
        s._simplified = SimplificationLevel.FULL_SIMPLIFY

        # dealing with annotations
        if e.annotations:
            ast_args = tuple(a for a in e.args if isinstance(a, Base))
            annotations = tuple(
                set(chain(from_iterable(a._relocatable_annotations for a in ast_args), tuple(a for a in e.annotations)))
            )
            if annotations != s.annotations:
                s = s.remove_annotations(s.annotations)
                s = s.annotate(*annotations)

        return s


# pylint:disable=wrong-import-position
from claripy.ast.bool import If, Not  # noqa: E402
