from __future__ import annotations

from . import backends, frontend_mixins, frontends


class Solver(
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
    """Solver is the default Claripy frontend. It uses Z3 as the backend solver by default."""

    def __init__(self, backend=backends.z3, **kwargs):
        super().__init__(backend, **kwargs)


class SolverCacheless(
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.EagerResolutionMixin,
    frontend_mixins.ConstraintFilterMixin,
    frontend_mixins.ConstraintDeduplicatorMixin,
    frontend_mixins.SimplifySkipperMixin,
    frontends.FullFrontend,
):
    """SolverCacheless is a Solver without caching. It uses Z3 as the backend solver by default."""

    def __init__(self, backend=backends.z3, **kwargs):
        super().__init__(backend, **kwargs)


class SolverReplacement(
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.ConstraintDeduplicatorMixin,
    frontends.ReplacementFrontend,
):
    """SolverReplacement is a frontend wrapper that replaces constraints with their solutions."""

    def __init__(self, actual_frontend=None, **kwargs):
        actual_frontend = Solver() if actual_frontend is None else actual_frontend
        super().__init__(actual_frontend, **kwargs)


class SolverHybrid(
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.EagerResolutionMixin,
    frontend_mixins.ConstraintFilterMixin,
    frontend_mixins.ConstraintDeduplicatorMixin,
    frontend_mixins.SimplifySkipperMixin,
    # TODO: frontend_mixins.ConstraintExpansionMixin,
    frontends.HybridFrontend,
):
    """SolverHybrid is a frontend that uses an exact solver and an approximate solver."""

    def __init__(
        self,
        exact_frontend=None,
        approximate_frontend=None,
        complex_auto_replace=True,
        replace_constraints=True,
        track=False,
        approximate_first=False,
        **kwargs,
    ):
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
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.ConstraintFilterMixin,
    frontends.LightFrontend,
):
    """SolverVSA is a thin frontend to the VSA backend solver."""

    def __init__(self, **kwargs):
        super().__init__(backends.vsa, **kwargs)


class SolverConcrete(
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.ConstraintFilterMixin,
    frontends.LightFrontend,
):
    """SolverConcrete is a thin frontend to the Concrete backend solver."""

    def __init__(self, **kwargs):
        super().__init__(backends.concrete, **kwargs)


class SolverStrings(
    # TODO: Figure ot if we need to use all these mixins
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.ConstraintFilterMixin,
    frontend_mixins.ConstraintDeduplicatorMixin,
    frontend_mixins.EagerResolutionMixin,
    frontends.FullFrontend,
):
    """SolverStrings is a frontend that uses Z3 to solve string constraints."""

    def __init__(self, *args, backend=backends.z3, **kwargs):
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
    """SolverCompositeChild is a frontend that is used as a child in a SolverComposite."""

    def __init__(self, backend=backends.z3, **kwargs):
        super().__init__(backend, **kwargs)

    def __repr__(self):
        return "<SolverCompositeChild with %d variables>" % len(self.variables)


class SolverComposite(
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
    """SolverComposite is a frontend that composes multiple templated frontends."""

    def __init__(self, template_solver=None, track=False, **kwargs):
        template_solver = SolverCompositeChild(track=track) if template_solver is None else template_solver
        super().__init__(template_solver, track=track, **kwargs)

    def __repr__(self):
        return "<SolverComposite %x, %d children>" % (id(self), len(self._solver_list))
