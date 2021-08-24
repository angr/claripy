/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "testlib.hpp"

/** Test the backend min and max functions */
void min_max() {
    z3::context ctx;
    auto z3 { Backend::Z3::Z3 {} };

    // (x-5)^2 - 5 = 0
    const auto x { Create::symbol<Expression::BV>("x", 64) };
    const auto five { Create::literal(5_ui) };
    const auto diff { Create::sub(x, five) };
    const auto quadratic { Create::sub(Create::mul({ diff, diff }), five) };
    const auto equation { Create::eq<Expression::BV>(quadratic, Create::literal(0_ui)) };

    // Construct the solver
    const auto solver { z3.new_tls_solver() };
    solver->add(z3.convert(equation));

    // Find min (should be -5 at x = 5).
    auto s { *solver.get() };
    const auto min { z3.min<true>(z3.convert(x), s) };

    Utils::Log::critical(min);
    UNITTEST_ASSERT(min == -5);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(min_max)