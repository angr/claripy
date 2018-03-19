#!/usr/bin/env python

import claripy
import ipdb
from IPython import embed
from claripy import frontend_mixins, frontends, backend_manager, backends
from claripy.backends.backend_smt_abc import BackendSMT_ABC
from claripy.backends.backend_smt_cvc4 import BackendSMT_CVC4

backend_abc = backend_manager.backends._register_backend(BackendSMT_ABC(), 'smt_abc', False, False)
backend_cvc4 = backend_manager.backends._register_backend(BackendSMT_CVC4(), 'smt_cvc4', False, False)

class SolverSMT_ABC(
    frontend_mixins.ConstraintFixerMixin,
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.ConstraintFilterMixin,
    frontend_mixins.ConstraintDeduplicatorMixin,
    frontend_mixins.EagerResolutionMixin,
    frontends.DumperFrontend
):
    def __init__(self, **kwargs):
        super(SolverSMT_ABC, self).__init__(backends.smt_abc, **kwargs)

class SolverSMT_CVC4(
    frontend_mixins.ConstraintFixerMixin,
    frontend_mixins.ConcreteHandlerMixin,
    frontend_mixins.ConstraintFilterMixin,
    frontend_mixins.ConstraintDeduplicatorMixin,
    frontend_mixins.EagerResolutionMixin,
    frontends.DumperFrontend
):
    def __init__(self, **kwargs):
        super(SolverSMT_CVC4, self).__init__(backends.smt_cvc4, **kwargs)


solverSMT_ABC = SolverSMT_ABC()
solverSMT_CVC4 = SolverSMT_CVC4()
solverz3 = claripy.Solver()

def test_backend_smt(solver):
    str_concrete = claripy.StringV("conc")
    str_concrete2 = claripy.StringV("con2")
    str_symbol = claripy.StringS("symb_concat", 4, explicit_name=True)
    str_symbol2 = claripy.StringS("symb_concat2", 4, explicit_name=True)
    solver.add(str_concrete == str_symbol)
    solver.add(str_concrete2 == str_symbol2)
    #ipdb.set_trace()
    result = solver.satisfiable()
    model = solver._solver_backend._get_model()
    solver.eval_to_ast(str_concrete)
    return result

def test_comparison_z3():
    solver = claripy.Solver()
    a = claripy.BVS('x', 32)
    b = claripy.BVS('y', 32)
    solver.add(a + b == 32)
    solver.add(claripy.And(b > 0, b < 10))
    result = solver.eval_to_ast(a + b, 10)
    print result
    return result

test_comparison_z3()
test_backend_smt(solverSMT_CVC4)


# if __name__ == "__main__":
#     suite = unittest.TestLoader().loadTestsFromTestCase(TestStringOperation)
#     unittest.TextTestRunner(verbosity=2).run(suite)

# # # --------------- LENGTH EXAMPLE ----------------

# # length = claripy.String.Length(str_concrete)
# # length_symb = claripy.String.Length(str_symbol)
# # solverSMT.add(length == claripy.StringV('a')) solverSMT.add(str_symbol[1:2] == claripy.StringV('a')) solverSMT.add(len(str_concrete) == 4)
# # ipdb.set_trace()
