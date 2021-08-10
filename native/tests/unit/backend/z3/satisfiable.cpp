/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "testlib.hpp"


/** Test is_true and is_false */
void satisfiable() {
    namespace Ex = Expression;
    using B = Ex::Bool;

    auto z3 { Backend::Z3::Z3 {} };
    auto solver { z3.new_tls_solver() };

    // Leaves
    const auto x { Create::symbol("x") };
    const auto t { Create::literal(true) };
    const auto f { Create::literal(false) };

    // Statements
    const auto true_ { Create::or_<B>({ x, t }) };
    const auto false_ { Create::and_<B>({ x, f }) };
    const auto maybe_true { Create::and_<B>({ x, t }) };
    const auto maybe_false { Create::or_<B>({ x, f }) };

    // Create a solver
    auto is_sat = [&x, &z3, &solver](const Ex::BasePtr &e, const Ex::BasePtr ec = nullptr) {
        solver->push();
        bool ret; // NOLINT
        if (ec != nullptr) {
            std::set<Expression::BasePtr> ecs;
            ecs.emplace(Create::eq<B>(x, ec));
            solver->add(z3.convert(e));
            ret = z3.satisfiable(solver, ecs);
        }
        else {
            solver->add(z3.convert(e));
            ret = z3.satisfiable(solver);
        }
        solver->pop();
        return ret;
    };

    // Test sat
    UNITTEST_ASSERT(is_sat(true_));
    UNITTEST_ASSERT(!is_sat(false_));
    UNITTEST_ASSERT(is_sat(maybe_true));
    UNITTEST_ASSERT(is_sat(maybe_false));

    // Test sat with extra constraints
    UNITTEST_ASSERT(is_sat(true_, f));
    UNITTEST_ASSERT(!is_sat(false_, f));
    UNITTEST_ASSERT(!is_sat(maybe_true, f));
    UNITTEST_ASSERT(is_sat(maybe_false, t));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(satisfiable)