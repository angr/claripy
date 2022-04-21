/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** Test is_true and is_false */
void solution() {

    auto z3 { Backend::Z3::Z3 {} };
    auto solver_ref { z3.tls_solver() };
    auto &solver { *solver_ref };

    // Leaves
    const auto x { Create::symbol_bool("x") };
    const auto t { Create::literal(true) };
    const auto f { Create::literal(false) };

    // Statements
    const auto maybe_true { Create::and_({ x, t }) };
    const auto maybe_false { Create::or_({ x, f }) };

    // Create a solver
    auto is_sol = [&x, &z3, &solver](const Expr::BasePtr &start, const Expr::BasePtr &x_s) {
        solver->push();
        z3.add(solver, start.get());
        const bool ret = z3.solution(x.get(), x_s.get(), solver);
        solver->pop();
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
