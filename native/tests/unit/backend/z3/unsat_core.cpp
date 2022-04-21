/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** Test the backend unsat_core function */
void unsat_core() {
    auto z3 { Backend::Z3::Z3 {} };

    // Prep
    auto lt { [](const U64 c) { return Create::literal(c); } };
    const auto solver_ref { z3.tls_solver() };
    auto &solver { *solver_ref };

    // Two contradictory exprs and one other
    const auto x { Create::symbol_bv("x", 64) };
    const auto xneq0 { Create::neq(x, lt(0)) };
    const auto xeq1 { Create::eq(x, lt(1)) };
    const auto make_xeq2 { [&x, &lt]() { return Create::eq(x, lt(2)); } };

    // Add all three constraints
    auto tmp_xeq2 { make_xeq2() };
    z3.add<true>(solver, xneq0.get()); // Should not end up in unsat-core
    z3.add<true>(solver, xeq1.get());
    z3.add<true>(solver, tmp_xeq2.get());

    // Release xeq2 to force reconstruction of it later
    UNITTEST_ASSERT(tmp_xeq2.use_count() == 1);
    tmp_xeq2.reset();

    // Verify unsatisfiability
    // Note: this should call solver.check(), which *must* be done before calling unsat_core
    UNITTEST_ASSERT(!z3.satisfiable(solver));

    // Test unsat core
    auto vec { z3.unsat_core(solver) }; // Should also reconstruct xeq1 via abstraction
    tmp_xeq2 = make_xeq2();             // Re-make
    UNITTEST_ASSERT(vec.size() == 2);   // Verify unsat core
    UNITTEST_ASSERT(vec[0] == xeq1 && vec[1] == tmp_xeq2); // Verify reconstruction + unsat core

    // Verify that untracked constraints don't end up in unsat_core
    solver->reset();
    z3.add<true>(solver, xeq1.get());
    z3.add<false>(solver, tmp_xeq2.get()); // xgeq2
    UNITTEST_ASSERT(!z3.satisfiable(solver));
    vec = z3.unsat_core(solver);
    UNITTEST_ASSERT(vec.size() == 1);
    UNITTEST_ASSERT(vec[0] = xeq1);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(unsat_core)
