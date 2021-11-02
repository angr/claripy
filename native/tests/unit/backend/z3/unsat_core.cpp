/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** Test the backend unsat_core function */
void unsat_core() {
    auto z3 { Backend::Z3::Z3 {} };

    // Prep
    auto lt { [](const uint64_t c) { return Create::literal(c); } };
    const auto solver_ref { z3.tls_solver() };
    auto &solver { *solver_ref };

    // Two contradictory exprs and one other
    const auto x { Create::symbol<Expr::BV>("x", 64) };
    const auto xneq0 { Create::neq(x, lt(0)) };
    const auto xeq1 { Create::eq(x, lt(1)) };
    const auto make_xeq2 { [&x, &lt]() { return Create::eq(x, lt(2)); } };

    // Add all three constraints
    auto tmp { make_xeq2() };
    z3.add<true>(solver, xneq0.get());
    z3.add<true>(solver, xeq1.get());
    z3.add<true>(solver, tmp.get()); // xgeq2

    // Release xeq2 to force reconstruction of it later
    UNITTEST_ASSERT(tmp.use_count() == 1);
    tmp.reset();

    // Verify unsatisfiability
    // Note: this should call solver.check(), which *must* be done before calling unsat_core
    UNITTEST_ASSERT(!z3.satisfiable(solver));

    // Test unsat core
    const auto vec { z3.unsat_core(solver) };
    UNITTEST_ASSERT(vec.size() == 2);
    UNITTEST_ASSERT(vec[0] == xeq1 && vec[1] == make_xeq2());
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(unsat_core)
