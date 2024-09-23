from __future__ import annotations

import claripy.backends as backends
import claripy.frontend as frontend
import claripy.frontend.mixin as mixin


class Solver(
    mixin.ConcreteHandlerMixin,
    mixin.EagerResolutionMixin,
    mixin.ConstraintFilterMixin,
    mixin.ConstraintDeduplicatorMixin,
    mixin.SimplifySkipperMixin,
    mixin.SatCacheMixin,
    mixin.ModelCacheMixin,
    mixin.ConstraintExpansionMixin,
    mixin.SimplifyHelperMixin,
    frontend.FullFrontend,
):
    """Solver is the default Claripy frontend. It uses Z3 as the backend solver by default."""

    def __init__(self, backend=backends.z3, **kwargs):
        super().__init__(backend, **kwargs)


class SolverCacheless(
    mixin.ConcreteHandlerMixin,
    mixin.EagerResolutionMixin,
    mixin.ConstraintFilterMixin,
    mixin.ConstraintDeduplicatorMixin,
    mixin.SimplifySkipperMixin,
    frontend.FullFrontend,
):
    """SolverCacheless is a Solver without caching. It uses Z3 as the backend solver by default."""

    def __init__(self, backend=backends.z3, **kwargs):
        super().__init__(backend, **kwargs)


class SolverReplacement(
    mixin.ConcreteHandlerMixin,
    mixin.ConstraintDeduplicatorMixin,
    frontend.ReplacementFrontend,
):
    """SolverReplacement is a frontend wrapper that replaces constraints with their solutions."""

    def __init__(self, actual_frontend=None, **kwargs):
        actual_frontend = Solver() if actual_frontend is None else actual_frontend
        super().__init__(actual_frontend, **kwargs)


class SolverHybrid(
    mixin.ConcreteHandlerMixin,
    mixin.EagerResolutionMixin,
    mixin.ConstraintFilterMixin,
    mixin.ConstraintDeduplicatorMixin,
    mixin.SimplifySkipperMixin,
    # TODO: mixin.ConstraintExpansionMixin,
    frontend.HybridFrontend,
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
    mixin.ConcreteHandlerMixin,
    mixin.ConstraintFilterMixin,
    frontend.LightFrontend,
):
    """SolverVSA is a thin frontend to the VSA backend solver."""

    def __init__(self, **kwargs):
        super().__init__(backends.vsa, **kwargs)


class SolverConcrete(
    mixin.ConcreteHandlerMixin,
    mixin.ConstraintFilterMixin,
    frontend.LightFrontend,
):
    """SolverConcrete is a thin frontend to the Concrete backend solver."""

    def __init__(self, **kwargs):
        super().__init__(backends.concrete, **kwargs)


class SolverStrings(
    # TODO: Figure ot if we need to use all these mixins
    mixin.ConcreteHandlerMixin,
    mixin.ConstraintFilterMixin,
    mixin.ConstraintDeduplicatorMixin,
    mixin.EagerResolutionMixin,
    frontend.FullFrontend,
):
    """SolverStrings is a frontend that uses Z3 to solve string constraints."""

    def __init__(self, *args, backend=backends.z3, **kwargs):
        super().__init__(backend, *args, **kwargs)


#
# Composite solving
#


class SolverCompositeChild(
    mixin.ConstraintDeduplicatorMixin,
    mixin.SatCacheMixin,
    mixin.SimplifySkipperMixin,
    mixin.ModelCacheMixin,
    frontend.FullFrontend,
):
    """SolverCompositeChild is a frontend that is used as a child in a SolverComposite."""

    def __init__(self, backend=backends.z3, **kwargs):
        super().__init__(backend, **kwargs)

    def __repr__(self):
        return "<SolverCompositeChild with %d variables>" % len(self.variables)


class SolverComposite(
    mixin.ConcreteHandlerMixin,
    mixin.EagerResolutionMixin,
    mixin.ConstraintFilterMixin,
    mixin.ConstraintDeduplicatorMixin,
    mixin.SatCacheMixin,
    mixin.SimplifySkipperMixin,
    mixin.SimplifyHelperMixin,
    mixin.ConstraintExpansionMixin,
    mixin.CompositedCacheMixin,
    frontend.CompositeFrontend,
):
    """SolverComposite is a frontend that composes multiple templated frontends."""

    def __init__(self, template_solver=None, track=False, **kwargs):
        template_solver = SolverCompositeChild(track=track) if template_solver is None else template_solver
        super().__init__(template_solver, track=track, **kwargs)

    def __repr__(self):
        return "<SolverComposite %x, %d children>" % (id(self), len(self._solver_list))
