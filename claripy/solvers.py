from . import frontend_mixins
from . import frontends
from . import backends

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
    frontends.FullFrontend
):
    def __init__(self, backend=backends.z3, **kwargs):
        super(Solver, self).__init__(backend, **kwargs)

class SolverCacheless(
    frontend_mixins.ConstraintFixerMixin,
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.EagerResolutionMixin,
    frontend_mixins.ConstraintFilterMixin,
    frontend_mixins.ConstraintDeduplicatorMixin,
    frontend_mixins.SimplifySkipperMixin,
    frontends.FullFrontend
):
    def __init__(self, backend=backends.z3, **kwargs):
        super(SolverCacheless, self).__init__(backend, **kwargs)

class SolverReplacement(
    frontend_mixins.ConstraintFixerMixin,
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.ConstraintDeduplicatorMixin,
    frontends.ReplacementFrontend
):
    def __init__(self, actual_frontend=None, **kwargs):
        actual_frontend = Solver() if actual_frontend is None else actual_frontend
        super(SolverReplacement, self).__init__(actual_frontend, **kwargs)

class SolverHybrid(
    frontend_mixins.ConstraintFixerMixin,
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.EagerResolutionMixin,
    frontend_mixins.ConstraintFilterMixin,
    frontend_mixins.ConstraintDeduplicatorMixin,
    frontend_mixins.SimplifySkipperMixin,
    # TODO: frontend_mixins.ConstraintExpansionMixin,
    frontends.HybridFrontend
):
    def __init__(
        self, exact_frontend=None, approximate_frontend=None,
        complex_auto_replace=True, replace_constraints=True,
        track=False, approximate_first=False,
        **kwargs
    ):
        exact_frontend = Solver(track=track) if exact_frontend is None else exact_frontend
        approximate_frontend = SolverReplacement(
            actual_frontend=SolverVSA(),
            complex_auto_replace=complex_auto_replace, replace_constraints=replace_constraints,
        ) if approximate_frontend is None else approximate_frontend
        super(SolverHybrid, self).__init__(
            exact_frontend, approximate_frontend, approximate_first=approximate_first, **kwargs
        )

class SolverVSA(
    frontend_mixins.ConstraintFixerMixin,
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.ConstraintFilterMixin,
    frontends.LightFrontend
):
    def __init__(self, **kwargs):
        super(SolverVSA, self).__init__(backends.vsa, **kwargs)

class SolverConcrete(
    frontend_mixins.ConstraintFixerMixin,
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.ConstraintFilterMixin,
    frontends.LightFrontend
):
    def __init__(self, **kwargs):
        super(SolverConcrete, self).__init__(backends.concrete, **kwargs)

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
    def __init__(self, backend, *args, **kwargs):
        super(SolverStrings, self).__init__(backend, *args, **kwargs)

#
# Composite solving
#

class SolverCompositeChild(
    frontend_mixins.ConstraintDeduplicatorMixin,
    frontend_mixins.SatCacheMixin,
    frontend_mixins.SimplifySkipperMixin,
    frontend_mixins.ModelCacheMixin,
    frontends.FullFrontend
):
    def __init__(self, backend=backends.z3, **kwargs):
        super(SolverCompositeChild, self).__init__(backend, **kwargs)

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
    frontends.CompositeFrontend
):
    def __init__(self, template_solver=None, track=False, template_solver_string=None, **kwargs):
        template_solver = SolverCompositeChild(track=track) if template_solver is None else template_solver
        template_solver_string = SolverCompositeChild(track=track, backend=backends.z3) if \
            template_solver_string is None else template_solver_string
        super(SolverComposite, self).__init__(template_solver, template_solver_string, track=track, **kwargs)

    def __repr__(self):
        return "<SolverComposite %x, %d children>" % (id(self), len(self._solver_list))
