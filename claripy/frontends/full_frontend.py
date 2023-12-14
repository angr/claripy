from typing import List, TYPE_CHECKING, overload, Tuple, Optional, Iterable, TypeVar, Any
import logging
import threading

from .constrained_frontend import ConstrainedFrontend

if TYPE_CHECKING:
    from ..ast.bv import BV
    from ..ast.bool import Bool
    from ..ast.fp import FP

l = logging.getLogger("claripy.frontends.full_frontend")

T = TypeVar("T", bound="FullFrontend")


class FullFrontend(ConstrainedFrontend):
    _model_hook = None

    def __init__(self, solver_backend, timeout=None, max_memory=None, track=False, **kwargs):
        ConstrainedFrontend.__init__(self, **kwargs)
        self._track = track
        self._solver_backend = solver_backend
        self.timeout = timeout if timeout is not None else 300000
        self.max_memory = max_memory
        self._tls = threading.local()
        self._to_add = []

    def _blank_copy(self, c):
        super()._blank_copy(c)
        c._track = self._track
        c._solver_backend = self._solver_backend
        c.timeout = self.timeout
        c.max_memory = self.max_memory
        c._tls = threading.local()
        c._to_add = []

    def _copy(self, c):
        super()._copy(c)
        c._track = self._track
        c._tls.solver = getattr(self._tls, "solver", None)  # pylint:disable=no-member
        c._to_add = list(self._to_add)

    #
    # Serialization support
    #

    def __getstate__(self):
        return (
            self._solver_backend.__class__.__name__,
            self.timeout,
            self.max_memory,
            self._track,
            super().__getstate__(),
        )

    def __setstate__(self, s):
        backend_name, self.timeout, self.max_memory, self._track, base_state = s
        self._solver_backend = backends._backends_by_type[backend_name]
        # self._tls = None
        self._tls = threading.local()
        self._to_add = []
        super().__setstate__(base_state)

    #
    # Frontend Creation
    #

    def _get_solver(self):
        if getattr(self._tls, "solver", None) is None:
            self._tls.solver = self._solver_backend.solver(timeout=self.timeout, max_memory=self.max_memory)
            self._add_constraints()
        elif self._finalized and len(self._to_add) > 0:
            if not hasattr(self._solver_backend, "clone_solver") or self._solver_backend.reuse_z3_solver:
                # this function may return a cached solver
                self._tls.solver = self._solver_backend.solver(timeout=self.timeout, max_memory=self.max_memory)
            else:
                self._tls.solver = self._solver_backend.clone_solver(self._tls.solver)
            self._add_constraints()

        if len(self._to_add) > 0:
            self._add_constraints()

        solver = self._tls.solver
        if self._solver_backend.reuse_z3_solver:
            # we must re-add all constraints
            self._add_constraints()
        return solver

    def _add_constraints(self):
        self._solver_backend.add(self._tls.solver, self.constraints, track=self._track)
        self._to_add = []

    #
    # Constraint management
    #

    def add(self, constraints: List["Bool"]) -> List["Bool"]:
        to_add = ConstrainedFrontend.add(self, constraints)
        self._to_add += to_add
        return to_add

    def simplify(self) -> List["Bool"]:
        ConstrainedFrontend.simplify(self)

        # TODO: should we do this?
        self._tls.solver = None
        self._to_add = []

        return self.constraints

    def check_satisfiability(self, extra_constraints=(), exact=None) -> bool:
        try:
            return self._solver_backend.check_satisfiability(
                extra_constraints=extra_constraints, solver=self._get_solver(), model_callback=self._model_hook
            )
        except BackendError as e:
            raise ClaripyFrontendError("Backend error during solve") from e

    def satisfiable(self, extra_constraints: Iterable["Bool"] = (), exact: Optional[bool] = None) -> bool:
        try:
            return self._solver_backend.satisfiable(
                extra_constraints=extra_constraints, solver=self._get_solver(), model_callback=self._model_hook
            )
        except BackendError as e:
            raise ClaripyFrontendError("Backend error during solve") from e

    @overload
    def eval(
        self, e: "BV", n: int, extra_constraints: Tuple["Bool", ...] = ..., exact: Optional["Bool"] = ...
    ) -> Tuple[int, ...]:
        ...

    @overload
    def eval(
        self, e: "Bool", n: int, extra_constraints: Tuple["Bool", ...] = ..., exact: Optional["Bool"] = ...
    ) -> Tuple[bool, ...]:
        ...

    @overload
    def eval(
        self, e: "FP", n: int, extra_constraints: Tuple["Bool", ...] = ..., exact: Optional["Bool"] = ...
    ) -> Tuple[float, ...]:
        ...

    def eval(self, e, n, extra_constraints=(), exact=None) -> Tuple[Any, ...]:
        if not self.satisfiable(extra_constraints=extra_constraints):
            raise UnsatError("unsat")

        try:
            return tuple(
                self._solver_backend.eval(
                    e,
                    n,
                    extra_constraints=extra_constraints,
                    solver=self._get_solver(),
                    model_callback=self._model_hook,
                )
            )
        except BackendError as exc:
            raise ClaripyFrontendError("Backend error during eval") from exc

    # this is technically wrong but we cannot do better because python doesn't have associated types
    # if you need another overload, add one
    @overload
    def batch_eval(
        self, exprs: Iterable["BV"], n: int, extra_constraints: Tuple["Bool", ...] = ..., exact: Optional[bool] = ...
    ) -> List[Tuple[int, ...]]:
        ...

    @overload
    def batch_eval(
        self, exprs: Iterable["Bool"], n: int, extra_constraints: Tuple["Bool", ...] = ..., exact: Optional[bool] = ...
    ) -> List[Tuple[bool, ...]]:
        ...

    @overload
    def batch_eval(
        self, exprs: Iterable["FP"], n: int, extra_constraints: Tuple["Bool", ...] = ..., exact: Optional[bool] = ...
    ) -> List[Tuple[float, ...]]:
        ...

    def batch_eval(self, exprs, n, extra_constraints=(), exact=None):
        if not self.satisfiable(extra_constraints=extra_constraints):
            raise UnsatError("unsat")

        try:
            return self._solver_backend.batch_eval(
                exprs,
                n,
                extra_constraints=extra_constraints,
                solver=self._get_solver(),
                model_callback=self._model_hook,
            )
        except BackendError as e:
            raise ClaripyFrontendError("Backend error during batch_eval") from e

    @overload
    def max(
        self, e: "BV", extra_constraints: Tuple["Bool", ...] = ..., signed: bool = ..., exact: Optional["Bool"] = ...
    ) -> int:
        ...

    @overload
    def max(
        self, e: "Bool", extra_constraints: Tuple["Bool", ...] = ..., signed: bool = ..., exact: Optional["Bool"] = ...
    ) -> bool:
        ...

    @overload
    def max(
        self, e: "FP", extra_constraints: Tuple["Bool", ...] = ..., signed: bool = ..., exact: Optional["Bool"] = ...
    ) -> float:
        ...

    def max(self, e, extra_constraints=(), signed=False, exact=None):
        if not self.satisfiable(extra_constraints=extra_constraints):
            raise UnsatError("Unsat during _max()")

        l.debug("Frontend.max() with %d extra_constraints", len(extra_constraints))

        # pylint: disable=unsubscriptable-object
        two = self.eval(e, 2, extra_constraints=extra_constraints)
        if len(two) == 0:
            raise UnsatError("unsat during max()")
        if len(two) == 1:
            return two[0]

        if signed:
            c = tuple(extra_constraints) + (SGE(e, two[0]), SGE(e, two[1]))
        else:
            c = tuple(extra_constraints) + (UGE(e, two[0]), UGE(e, two[1]))
        try:
            return self._solver_backend.max(
                e,
                extra_constraints=c,
                solver=self._get_solver(),
                model_callback=self._model_hook,
                signed=signed,
            )
        except BackendError as exc:
            raise ClaripyFrontendError("Backend error during max") from exc

    @overload
    def min(
        self, e: "BV", extra_constraints: Tuple["Bool", ...] = ..., signed: bool = ..., exact: Optional["Bool"] = ...
    ) -> int:
        ...

    @overload
    def min(
        self, e: "Bool", extra_constraints: Tuple["Bool", ...] = ..., signed: bool = ..., exact: Optional["Bool"] = ...
    ) -> bool:
        ...

    @overload
    def min(
        self, e: "FP", extra_constraints: Tuple["Bool", ...] = ..., signed: bool = ..., exact: Optional["Bool"] = ...
    ) -> float:
        ...

    def min(self, e, extra_constraints=(), signed=False, exact=None):
        if not self.satisfiable(extra_constraints=extra_constraints):
            raise UnsatError("Unsat during _min()")

        l.debug("Frontend.min() with %d extra_constraints", len(extra_constraints))

        # pylint: disable=unsubscriptable-object
        two = self.eval(e, 2, extra_constraints=extra_constraints)
        if len(two) == 0:
            raise UnsatError("unsat during min()")
        if len(two) == 1:
            return two[0]

        if signed:
            c = tuple(extra_constraints) + (SLE(e, two[0]), SLE(e, two[1]))
        else:
            c = tuple(extra_constraints) + (ULE(e, two[0]), ULE(e, two[1]))
        try:
            return self._solver_backend.min(
                e,
                extra_constraints=c,
                solver=self._get_solver(),
                model_callback=self._model_hook,
                signed=signed,
            )
        except BackendError as exc:
            raise ClaripyFrontendError("Backend error during min") from exc

    @overload
    def solution(
        self, e: "BV", v: int, extra_constraints: Tuple["Bool", ...] = ..., exact: Optional["Bool"] = ...
    ) -> bool:
        ...

    @overload
    def solution(
        self, e: "Bool", v: bool, extra_constraints: Tuple["Bool", ...] = ..., exact: Optional["Bool"] = ...
    ) -> bool:
        ...

    @overload
    def solution(
        self, e: "FP", v: float, extra_constraints: Tuple["Bool", ...] = ..., exact: Optional["Bool"] = ...
    ) -> bool:
        ...

    def solution(self, e, v, extra_constraints=(), exact=None):
        try:
            return self._solver_backend.solution(
                e, v, extra_constraints=extra_constraints, solver=self._get_solver(), model_callback=self._model_hook
            )
        except BackendError as exc:
            raise ClaripyFrontendError("Backend error during solution") from exc

    def is_true(self, e: "Bool", extra_constraints: Tuple["Bool", ...] = (), exact: Optional[bool] = None) -> bool:
        return e.is_true()

    def is_false(self, e: "Bool", extra_constraints: Tuple["Bool", ...] = (), exact: Optional[bool] = None) -> bool:
        return e.is_false()

    def unsat_core(self, extra_constraints: Tuple["Bool", ...] = ()) -> Iterable["Bool"]:
        if self.satisfiable(extra_constraints=extra_constraints):
            # all constraints are satisfied
            return ()

        unsat_core = self._solver_backend.unsat_core(self._get_solver())

        return tuple(unsat_core)

    #
    # Serialization and such.
    #

    def downsize(self) -> None:
        ConstrainedFrontend.downsize(self)
        self._tls.solver = None
        self._to_add = []

    #
    # Merging and splitting
    #

    def merge(self: T, others, merge_conditions, common_ancestor=None) -> Tuple[bool, T]:
        return (
            self._solver_backend.__class__.__name__ == "BackendZ3",
            ConstrainedFrontend.merge(self, others, merge_conditions, common_ancestor=common_ancestor)[1],
        )


from ..errors import UnsatError, BackendError, ClaripyFrontendError
from ..ast.bv import UGE, ULE, SGE, SLE
from ..backend_manager import backends
