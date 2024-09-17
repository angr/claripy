from __future__ import annotations

import itertools
import logging
import math
import pickle
import struct
from collections import deque
from contextlib import suppress
from enum import IntEnum
from hashlib import blake2b
from itertools import chain
from typing import TYPE_CHECKING, Generic, NoReturn, TypeVar, Union, cast
from weakref import WeakValueDictionary

from typing_extensions import Self

from claripy import operations, simplifications
from claripy.backend_manager import backends
from claripy.errors import BackendError, ClaripyOperationError, ClaripyReplacementError
from claripy.fp import FSort

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Iterator

    from claripy import Backend
    from claripy.annotation import Annotation

l = logging.getLogger("claripy.ast")

blake2b_unpacker = struct.Struct("Q")
from_iterable = chain.from_iterable

# pylint:disable=unused-argument,too-many-boolean-expressions

ArgType = Union["Base", bool, int, float, str, FSort, tuple["ArgType"], None]

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
    _hash: int
    _simplified: SimplificationLevel
    _uneliminatable_annotations: frozenset[Annotation]

    # Backend information
    _errored: set[Backend]

    # Caching
    _ast_cache_key: ASTCacheKey[Self]
    _cached_encoded_name: bytes | None

    # Extra information
    _excavated: Base | None
    _burrowed: Base | None
    _uninitialized: bool

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
        "_errored",
        "_cache_key",
        "_cached_encoded_name",
        "_excavated",
        "_burrowed",
        "_uninitialized",
        "__weakref__",
    ]

    _hash_cache: WeakValueDictionary[int, Base] = WeakValueDictionary()

    def __new__(  # pylint:disable=redefined-builtin
        cls: type[Base],
        op: str,
        args: Iterable[ArgType],
        add_variables: Iterable[str] | None = None,
        hash: int | None = None,
        symbolic: bool | None = None,
        variables: frozenset[str] | None = None,
        errored: set[Backend] | None = None,
        uninitialized: bool | None = None,
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
        :param annotations:         A frozenset of annotations applied onto this AST.
        """

        if hash is not None and (self := cls._hash_cache.get(hash, None)) is not None:
            return self

        # if any(isinstance(a, BackendObject) for a in args):
        #   raise Exception('asdf')

        a_args = args if type(args) is tuple else tuple(args)
        b_args = tuple(a for a in a_args if isinstance(a, Base))

        if symbolic is None:
            symbolic = any(a.symbolic for a in b_args)
        if variables is None:
            variables = frozenset(chain.from_iterable(a.variables for a in b_args))
        if errored is None:
            errored = set(chain.from_iterable(a._errored for a in b_args))
        arg_max_depth = max((a.depth for a in b_args), default=0)

        if add_variables:
            variables = frozenset.union(variables, add_variables)

        if not symbolic and op not in operations.leaf_operations:
            with suppress(BackendError):
                r = operations._handle_annotations(backends.concrete._abstract(backends.concrete.call(op, args)), args)
                if r is not None:
                    return r

        uneliminatable_annotations = frozenset(a for a in annotations if not (a.eliminatable or a.relocatable))
        relocatable_annotations = frozenset(a for a in annotations if not a.eliminatable and a.relocatable)

        if not skip_child_annotations:
            for a in b_args:
                uneliminatable_annotations |= a._uneliminatable_annotations
                relocatable_annotations |= a._relocatable_annotations

            annotations = tuple(frozenset((*annotations, *relocatable_annotations)))

        hash_ = Base._calc_hash(op, a_args, annotations, length)
        self = cls._hash_cache.get(hash_, None)
        if self is None:
            self = super().__new__(cls)
            depth = arg_max_depth + 1
            self.__a_init__(
                op,
                a_args,
                variables,
                symbolic=symbolic,
                length=length,
                errored=errored,
                uninitialized=uninitialized,
                annotations=annotations,
                encoded_name=encoded_name,
                depth=depth,
                uneliminatable_annotations=uneliminatable_annotations,
                relocatable_annotations=relocatable_annotations,
            )
            self._hash = hash_
            cls._hash_cache[hash_] = self
        # else:
        #     if not self._check_args_same(a_args) or self.op != op or self.annotations != annotations:
        #         raise Exception("CRAP -- hash collision")

        return self

    def make_like(
        self,
        op: str,
        args: Iterable[ArgType],
        simplify: bool = False,
        annotations: tuple[Annotation, ...] | None = None,
        variables: frozenset[str] | None = None,
        symbolic: bool | None = None,
        uninitialized: bool | None = None,
        skip_child_annotations: bool = False,
        length: int | None = None,
    ) -> Self:
        # Try to simplify the expression again
        simplified = simplifications.simplify(op, args) if simplify else None
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
            h = Base._calc_hash(op, args, annotations, length)
            cached_ast = cast(T | None, cache.get(h, None))
            if cached_ast is not None:
                return cached_ast

            result: T = super().__new__(type(self))
            result.__a_init__(
                op,
                args,
                self.variables,
                depth=self.depth,
                uneliminatable_annotations=uneliminatable_annotations,
                relocatable_annotations=relocatable_annotations,
                symbolic=self.symbolic,
                annotations=annotations,
                length=length,
                uninitialized=self._uninitialized,
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

    # pylint:disable=attribute-defined-outside-init
    def __a_init__(
        self,
        op: str,
        args: tuple[ArgType, ...],
        variables: frozenset[str],
        symbolic: bool | None = None,
        length: int | None = None,
        simplified: SimplificationLevel = SimplificationLevel.UNSIMPLIFIED,
        errored: set[Backend] | None = None,
        uninitialized: bool | None = None,
        annotations: tuple[Annotation, ...] | None = None,
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
        self.variables = variables
        self.symbolic = symbolic
        self.annotations: tuple[Annotation] = annotations
        self._uneliminatable_annotations = uneliminatable_annotations
        self._relocatable_annotations = relocatable_annotations

        self.depth = depth if depth is not None else 1

        self._cached_encoded_name = encoded_name

        self._errored = errored if errored is not None else set()

        self._simplified = simplified
        self._cache_key = ASTCacheKey(self)
        self._excavated = None
        self._burrowed = None

        self._uninitialized = uninitialized

        if len(self.args) == 0:
            raise ClaripyOperationError("AST with no arguments!")

    # pylint:enable=attribute-defined-outside-init
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
        annotations: tuple[Annotation, ...],
        length: int | None,
    ) -> int:
        """
        Calculates the hash of an AST, given the operation, args, and kwargs.

        :param op:                  The operation.
        :param args:                The args tuple.
        :param annotations:         The annotations tuple.
        :returns:                   a hash, as bytes.

        We do it using md5 to avoid hash collisions.
        (hash(-1) == hash(-2), for example)
        """
        # HASHCONS: these attributes key the cache
        # BEFORE CHANGING THIS, SEE ALL OTHER INSTANCES OF "HASHCONS" IN THIS FILE

        to_hash = Base._ast_serialize(op, args, annotations, length)

        hd = blake2b(to_hash, digest_size=8).digest()
        return blake2b_unpacker.unpack(hd)[0]

    @staticmethod
    def _ast_serialize(
        op: str,
        args: tuple[ArgType, ...],
        annotations: tuple[Annotation, ...],
        length: int | None,
    ) -> bytes:
        """
        Serialize the AST and get a bytestring for hashing.

        :param op:          The operator.
        :param args:        The args tuple.
        :param annotations: The annotations tuple.
        :return:            The serialized bytestring.
        """

        serialized_args = b"".join(b"<" + Base._arg_serialize(a) + b">" for a in args)
        serialized_annotations = b"".join(b"(" + Base._arg_serialize(a) + b")" for a in annotations)
        serialized_length = b"" if length is None else length.to_bytes(8, "little", signed=False)

        return b"{" + op.encode() + serialized_args + serialized_annotations + serialized_length + b"}"

    @staticmethod
    def _arg_serialize(arg: ArgType | Annotation) -> bytes:
        """Serialize one argument."""

        if isinstance(arg, Base):
            return arg._hash.to_bytes(8, "little", signed=False)
        if arg is None:
            return b"\x0f"
        if arg is True:
            return b"\x1f"
        if arg is False:
            return b"\x2e"
        if isinstance(arg, int):
            return arg.to_bytes((arg.bit_length() + 15) // 8, "little", signed=True)
        if isinstance(arg, str):
            return arg.encode()
        if isinstance(arg, float):
            if math.isnan(arg):
                return b"nan"
            if math.isinf(arg):
                return b"inf"
            if arg == 0.0 and math.copysign(1, arg) < 0:
                return b"-0.0"
            return struct.pack("d", arg)
        if isinstance(arg, tuple):
            return b"".join(b"<" + Base._arg_serialize(a) + b">" for a in arg)
        if hasattr(arg, "__hash__"):
            return hash(arg).to_bytes(8, "little", signed=True)

        l.debug("Don't know how to serialize %s, consider implementing __hash__", arg)
        return pickle.dumps(arg)

    def __hash__(self) -> int:
        return self._hash

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

    def _check_args_same(self, other_args: tuple[ArgType, ...], lenient_names=False) -> bool:
        """
        Check if two ASTs are the same.
        """
        from claripy.vsa.strided_interval import StridedInterval  # pylint:disable=import-outside-toplevel

        # Several types inside of args don't support normall == comparison, so if we see those,
        # we need compare them manually.
        for a, b in zip(self.args, other_args, strict=True):
            if isinstance(a, Base) and isinstance(b, Base):
                if a._hash != b._hash:
                    return False
                continue
            if isinstance(a, float) and isinstance(b, float):
                if math.isnan(a) and math.isnan(b):
                    continue
                if math.isinf(a) and math.isinf(b):
                    continue
                if a != b:
                    return False
            if (
                isinstance(a, StridedInterval)
                and isinstance(b, StridedInterval)
                and (
                    a.bits != b.bits
                    or a.lower_bound != b.lower_bound
                    or a.upper_bound != b.upper_bound
                    or a.stride != b.stride
                )
            ):
                return False
            if lenient_names and isinstance(a, str) and isinstance(b, str):
                continue
            if a != b:
                return False

        return True

    def identical(self, other: Self, strict=False) -> bool:
        """
        Check if two ASTs are identical. If `strict` is False, the comparison
        will be lenient on the names of the ASTs.
        """
        return self._hash == other._hash or (
            self.op == other.op
            and self._check_args_same(other.args, lenient_names=not strict)
            and self.annotations == other.annotations
        )

    #
    # Collapsing and simplification
    #

    def _rename(self, new_name: str) -> Self:
        if self.op not in {"BVS", "BoolS", "FPS"}:
            raise ClaripyOperationError("rename is only supported on leaf nodes")
        new_args = (new_name,) + self.args[1:]
        return self.make_like(self.op, new_args, length=self.length, variables=frozenset((new_name,)))

    #
    # Annotations
    #

    def _apply_to_annotations(self, f):
        return self.make_like(self.op, self.args, annotations=f(self.annotations), skip_child_annotations=True)

    def has_annotation_type(self, annotation_type: type[Annotation]) -> bool:
        """
        Check if this AST has an annotation of a given type.

        :param annotation_type:     The type of the annotation.
        :return:                    True if the AST has an annotation of the given type.
        """
        return any(isinstance(a, annotation_type) for a in self.annotations)

    def get_annotations_by_type(self, annotation_type: type[Annotation]) -> tuple[Annotation, ...]:
        """
        Get all annotations of a given type.

        :param annotation_type:     The type of the annotation.
        :return:                    A tuple of annotations of the given type.
        """
        return tuple(a for a in self.annotations if isinstance(a, annotation_type))

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

    def clear_annotation_type(self, annotation_type: type[Annotation]) -> Self:
        """
        Removes all annotations of a given type from this AST.

        :param annotation_type:     the type of annotations to remove
        :returns:                   a new AST, with the annotations removed
        """
        return self._apply_to_annotations(
            lambda alist: tuple(oa for oa in alist if not isinstance(oa, annotation_type))
        )

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

        if self.op in operations.reversed_ops:
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

            if op == "BoolV":
                return str(args[0])

            if op == "BVV":
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

            if op == "Not":
                return f"!{args[0]}"

            if op == "Extract":
                return f"{args[2]}[{args[0]}:{args[1]}]"

            if op == "ZeroExt":
                value = f"0#{args[0]} .. {args[1]}"
                return f"({value})" if inner else value

            if op in operations.prefix:
                assert len(args) == 1
                value = f"{operations.prefix[op]}{args[0]}"
                return f"({value})" if inner and inner_infix_use_par else value

            if op in operations.infix:
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

    def is_leaf(self) -> bool:
        """
        Check if this AST is a leaf node.
        """
        return self.depth == 1

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

        if len(self.args) == len(new_args) and all(a is b for a, b in zip(self.args, new_args, strict=False)):
            return self

        length = self.length if new_length is None else new_length
        return self.make_like(self.op, new_args, length=length, **kwargs)

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

    def structurally_match(self, o: Base) -> bool:
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

        for arg_a, arg_b in zip(self.args, o.args, strict=False):
            if not isinstance(arg_a, Base):
                if type(arg_a) != type(arg_b):  # noqa: E721
                    return False
                # They are not ASTs
                if arg_a != arg_b:
                    return False
                continue

            if arg_a.is_leaf():
                if arg_a is not arg_b:
                    return False

            else:
                if not arg_a.structurally_match(arg_b):
                    return False

        return True

    def replace_dict(
        self, replacements, variable_set: set[str] | None = None, leaf_operation: Callable[[Base], Base] = lambda x: x
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
                    if ast.is_leaf():
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
                    if any((a is not b for a, b in zip(ast.args, args, strict=False))):
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

        if any(a.is_leaf() for a in self.args):
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

                if ast.is_leaf():
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
            raw = backends.concrete.convert(self)
            if isinstance(raw, bool):
                return raw
            return raw.value
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


def simplify(e: T) -> T:
    if isinstance(e, Base) and e.is_leaf():
        return e

    s = e._first_backend("simplify")
    if s is None:
        l.debug("Unable to simplify expression")
        return e

    # Copy some parameters (that should really go to the Annotation backend)
    s._uninitialized = e.uninitialized
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


# pylint:disable=wrong-import-position,ungrouped-imports
from claripy.ast.bool import If, Not  # noqa: E402
