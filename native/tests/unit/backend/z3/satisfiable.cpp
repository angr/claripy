/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** Test is_true and is_false */
void satisfiable() {

    auto z3 { Backend::Z3::Z3 {} };
    auto solver_ref { z3.tls_solver() };
    auto &solver { *solver_ref };

    // Leaves
    const auto x { Create::symbol_bool("x") };
    const auto t { Create::literal(true) };
    const auto f { Create::literal(false) };

    // Statements
    const auto true_ { Create::or_({ x, t }) };
    const auto false_ { Create::and_({ x, f }) };
    const auto and_true { Create::and_({ x, t }) };
    const auto or_false { Create::or_({ x, f }) };

    // Create a solver
    auto is_sat = [&x, &z3, &solver](const Expr::BasePtr &e,
                                     const Expr::BasePtr ec = nullptr) { // NOLINT
        solver->push();
        bool ret; // NOLINT
        if (ec) {
            std::vector<Expr::RawPtr> ecs;
            const auto c { Create::eq(x, ec) };
            ecs.emplace_back(c.get());
            z3.add(solver, e.get());
            ret = z3.satisfiable(solver, ecs);
        }
        else {
            z3.add(solver, e.get());
            ret = z3.satisfiable(solver);
        }
        solver->pop();
        return ret;
    };

    // Test sat
    UNITTEST_ASSERT(is_sat(true_));
    UNITTEST_ASSERT(not is_sat(false_));
    UNITTEST_ASSERT(is_sat(and_true));
    UNITTEST_ASSERT(is_sat(or_false));

    // Test sat with extra constraints
    UNITTEST_ASSERT(is_sat(true_, f));
    UNITTEST_ASSERT(is_sat(or_false, t));
    UNITTEST_ASSERT(not is_sat(false_, f));
    UNITTEST_ASSERT(not is_sat(and_true, f));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(satisfiable)
