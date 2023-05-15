from __future__ import annotations
from typing import TYPE_CHECKING
from . import frontend_mixins
from . import frontends
from . import backends

if TYPE_CHECKING:
    from claripy.backends.backend_smtlib_solvers.abc_popen import SolverBackendABC
    from claripy.backends.backend_smtlib_solvers.cvc4_popen import SolverBackendCVC4
    from claripy.backends.backend_z3 import BackendZ3


class Solver(
    frontend_mixins.ConstraintFixerMixin,
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.EagerResolutionMixin,
    frontend_mixins.ConstraintFilterMixin,
    frontend_mixins.ConstraintDeduplicatorMixin,
    frontend_mixins.SimplifySkipperMixin,
    frontend_mixins.SatCacheMixin,
    frontend_mixins.ModelCacheMixin,
    frontend_mixins.ConstraintExpansionMixin,
    frontend_mixins.SimplifyHelperMixin,
    frontends.FullFrontend,
):
    def __init__(self, backend: BackendZ3 = backends.z3, **kwargs) -> None:
        super().__init__(backend, **kwargs)


class SolverCacheless(
    frontend_mixins.ConstraintFixerMixin,
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.EagerResolutionMixin,
    frontend_mixins.ConstraintFilterMixin,
    frontend_mixins.ConstraintDeduplicatorMixin,
    frontend_mixins.SimplifySkipperMixin,
    frontends.FullFrontend,
):
    def __init__(self, backend: BackendZ3 = backends.z3, **kwargs) -> None:
        super().__init__(backend, **kwargs)


class SolverReplacement(
    frontend_mixins.ConstraintFixerMixin,
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.ConstraintDeduplicatorMixin,
    frontends.ReplacementFrontend,
):
    def __init__(self, actual_frontend: Solver | SolverVSA | None = None, **kwargs) -> None:
        actual_frontend = Solver() if actual_frontend is None else actual_frontend
        super().__init__(actual_frontend, **kwargs)


class SolverHybrid(
    frontend_mixins.ConstraintFixerMixin,
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.EagerResolutionMixin,
    frontend_mixins.ConstraintFilterMixin,
    frontend_mixins.ConstraintDeduplicatorMixin,
    frontend_mixins.SimplifySkipperMixin,
    # TODO: frontend_mixins.ConstraintExpansionMixin,
    frontends.HybridFrontend,
):
    def __init__(
        self,
        exact_frontend: None = None,
        approximate_frontend: None = None,
        complex_auto_replace: bool = True,
        replace_constraints: bool = True,
        track: bool = False,
        approximate_first: bool = False,
        **kwargs,
    ) -> None:
        exact_frontend = Solver(track=track) if exact_frontend is None else exact_frontend
        approximate_frontend = (
            SolverReplacement(
                actual_frontend=SolverVSA(),
                complex_auto_replace=complex_auto_replace,
                replace_constraints=replace_constraints,
            )
            if approximate_frontend is None
            else approximate_frontend
        )
        super().__init__(exact_frontend, approximate_frontend, approximate_first=approximate_first, **kwargs)


class SolverVSA(
    frontend_mixins.ConstraintFixerMixin,
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.ConstraintFilterMixin,
    frontends.LightFrontend,
):
    def __init__(self, **kwargs) -> None:
        super().__init__(backends.vsa, **kwargs)


class SolverConcrete(
    frontend_mixins.ConstraintFixerMixin,
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.ConstraintFilterMixin,
    frontends.LightFrontend,
):
    def __init__(self, **kwargs):
        super().__init__(backends.concrete, **kwargs)


class SolverStrings(
    # TODO: Figure ot if we need to use all these mixins
    frontend_mixins.ConstraintFixerMixin,
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.ConstraintFilterMixin,
    frontend_mixins.ConstraintDeduplicatorMixin,
    frontend_mixins.EagerResolutionMixin,
    frontend_mixins.EvalStringsToASTsMixin,
    frontend_mixins.SMTLibScriptDumperMixin,
    frontends.FullFrontend,
):
    def __init__(self, backend: SolverBackendABC | SolverBackendCVC4, *args, **kwargs) -> None:
        super().__init__(backend, *args, **kwargs)


#
# Composite solving
#


class SolverCompositeChild(
    frontend_mixins.ConstraintDeduplicatorMixin,
    frontend_mixins.SatCacheMixin,
    frontend_mixins.SimplifySkipperMixin,
    frontend_mixins.ModelCacheMixin,
    frontends.FullFrontend,
):
    def __init__(self, backend: SolverBackendCVC4 | BackendZ3 = backends.z3, **kwargs) -> None:
        super().__init__(backend, **kwargs)

    def __repr__(self):
        return "<SolverCompositeChild with %d variables>" % len(self.variables)


class SolverComposite(
    frontend_mixins.ConstraintFixerMixin,
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.EagerResolutionMixin,
    frontend_mixins.ConstraintFilterMixin,
    frontend_mixins.ConstraintDeduplicatorMixin,
    frontend_mixins.SatCacheMixin,
    frontend_mixins.SimplifySkipperMixin,
    frontend_mixins.SimplifyHelperMixin,
    frontend_mixins.ConstraintExpansionMixin,
    frontend_mixins.CompositedCacheMixin,
    frontends.CompositeFrontend,
):
    def __init__(
        self,
        template_solver: None = None,
        track: bool = False,
        template_solver_string: SolverCompositeChild | None = None,
        **kwargs,
    ) -> None:
        template_solver = SolverCompositeChild(track=track) if template_solver is None else template_solver
        template_solver_string = (
            SolverCompositeChild(track=track, backend=backends.z3)
            if template_solver_string is None
            else template_solver_string
        )
        super().__init__(template_solver, template_solver_string, track=track, **kwargs)

    def __repr__(self):
        return "<SolverComposite %x, %d children>" % (id(self), len(self._solver_list))
