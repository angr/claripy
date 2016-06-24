from . import frontends
from . import backends

class Solver(
    frontends.AddListMixin,
    frontends.ConcreteHandlerMixin,
    frontends.EagerResolutionMixin,
    frontends.ConstraintFilterMixin,
    frontends.ConstraintDeduplicatorMixin,
    frontends.ModelCacheMixin,
    frontends.ConstraintExpansionMixin,
    frontends.SimplifyHelperMixin,
    frontends.FullFrontend
):
    def __init__(self, backend=backends.z3, **kwargs):
        super(Solver, self).__init__(backend, **kwargs)

class SolverCacheless(
    frontends.AddListMixin,
    frontends.ConcreteHandlerMixin,
    frontends.EagerResolutionMixin,
    frontends.ConstraintFilterMixin,
    frontends.ConstraintDeduplicatorMixin,
    frontends.FullFrontend
):
    def __init__(self, backend=backends.z3, **kwargs):
        super(SolverCacheless, self).__init__(backend, **kwargs)

class SolverReplacement(
    frontends.AddListMixin,
    frontends.ConcreteHandlerMixin,
    frontends.ConstraintDeduplicatorMixin,
    frontends.ReplacementFrontend
):
    def __init__(self, actual_frontend=None, **kwargs):
        actual_frontend = Solver() if actual_frontend is None else actual_frontend
        super(SolverReplacement, self).__init__(actual_frontend, **kwargs)

class SolverHybrid(
    frontends.AddListMixin,
    frontends.ConcreteHandlerMixin,
    frontends.EagerResolutionMixin,
    frontends.ConstraintFilterMixin,
    frontends.ConstraintDeduplicatorMixin,
    frontends.HybridFrontend
):
    def __init__(
        self, exact_frontend=None, approximate_frontend=None,
        complex_auto_replace=True, replace_constraints=True,
        **kwargs
    ):
        exact_frontend = Solver() if exact_frontend is None else exact_frontend
        approximate_frontend = SolverReplacement(
            actual_frontend=SolverVSA(),
            complex_auto_replace=complex_auto_replace, replace_constraints=replace_constraints,
        ) if approximate_frontend is None else approximate_frontend
        super(SolverHybrid, self).__init__(exact_frontend, approximate_frontend, **kwargs)

class SolverComposite(
    frontends.AddListMixin,
    frontends.ConcreteHandlerMixin,
    frontends.EagerResolutionMixin,
    frontends.ConstraintFilterMixin,
    frontends.ConstraintDeduplicatorMixin,
    frontends.ConstraintExpansionMixin,
    frontends.CompositeFrontend
):
    def __init__(self, template_solver=None, **kwargs):
        template_solver = Solver() if template_solver is None else template_solver
        super(SolverComposite, self).__init__(template_solver, **kwargs)

class SolverVSA(
    frontends.AddListMixin,
    frontends.ConcreteHandlerMixin,
    frontends.ConstraintFilterMixin,
    frontends.LightFrontend
):
    def __init__(self, **kwargs):
        super(SolverVSA, self).__init__(backends.vsa, **kwargs)

class SolverConcrete(
    frontends.AddListMixin,
    frontends.ConcreteHandlerMixin,
    frontends.ConstraintFilterMixin,
    frontends.LightFrontend
):
    def __init__(self, **kwargs):
        super(SolverConcrete, self).__init__(backends.concrete, **kwargs)
