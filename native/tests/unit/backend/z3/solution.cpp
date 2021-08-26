/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "testlib.hpp"


/** Test is_true and is_false */
void solution() {
    namespace Ex = Expression;
    using B = Ex::Bool;

    auto z3 { Backend::Z3::Z3 {} };
    auto solver_ref { z3.new_tls_solver() };
    auto &solver { *solver_ref };

    // Leaves
    const auto x { Create::symbol("x") };
    const auto t { Create::literal(true) };
    const auto f { Create::literal(false) };

    // Statements
    const auto maybe_true { Create::and_<B>({ x, t }) };
    const auto maybe_false { Create::or_<B>({ x, f }) };

    // Create a solver
    auto is_sol = [&x, &z3, &solver](const Ex::BasePtr &start, const Ex::BasePtr &x_s) {
        solver.push();
        solver.add(z3.convert(start));
        const bool ret = z3.solution(x, x_s, solver);
        solver.pop();
        return ret;
    };

    // Test sat
    UNITTEST_ASSERT(is_sol(maybe_true, t));
    UNITTEST_ASSERT(!is_sol(maybe_true, f));
    UNITTEST_ASSERT(is_sol(maybe_false, t));
    UNITTEST_ASSERT(!is_sol(maybe_false, f));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(solution)