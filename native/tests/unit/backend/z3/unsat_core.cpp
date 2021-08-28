/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "testlib.hpp"

/** Test the backend unsat_core function */
void unsat_core() {
    auto z3 { Backend::Z3::Z3 {} };
    namespace Ex = Expression;

    // Prep
    auto lt { [](const uint64_t c) { return Create::literal(c); } };
    const auto solver_ref { z3.tls_solver() };
    auto &solver { *solver_ref };

    // Two contradictory expressions and one other
    const auto x { Create::symbol<Ex::BV>("x", 64) };
    const auto xneq0 { Create::neq<Ex::BV>(x, lt(0)) };
    const auto xeq1 { Create::eq<Ex::BV>(x, lt(1)) };
    const auto xeq2 { Create::eq<Ex::BV>(x, lt(2)) };
    const auto xx { Create::eq<Ex::BV>(x, Create::sub(x, lt(1))) };

    // Add all three constraints
    z3.add(solver, xneq0.get());
    z3.add(solver, xeq1.get());
    z3.add(solver, xeq2.get());
    z3.add(solver, xx.get());

    // Verify unsatisfiability
    // Note: this should call solver.check(), which *must* be done before calling unsat_core
    UNITTEST_ASSERT(!z3.satisfiable(solver));

    // Test unsat core
    const auto vec { z3.unsat_core(solver) };
    Utils::Log::debug(vec.size());
    UNITTEST_ASSERT(vec.size() == 2);
    Utils::Log::debug(vec[0]);
    Utils::Log::debug(vec[1]);
    UNITTEST_ASSERT(vec[0] == xeq1 && vec[1] == xeq2);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(unsat_core)
