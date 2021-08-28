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
    auto solver_ref { z3.tls_solver() };
    auto &solver { *solver_ref };

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
    using EBP = Ex::BasePtr;
    auto is_sat = [&x, &z3, &solver](const EBP &e, const EBP ec = nullptr) { // NOLINT
        solver.push();
        bool ret; // NOLINT
        if (ec != nullptr) {
            std::vector<EBP> ecs;
            ecs.emplace_back(Create::eq<B>(x, ec));
            z3.add(solver, e.get());
            ret = z3.satisfiable(solver, ecs);
        }
        else {
            z3.add(solver, e.get());
            ret = z3.satisfiable(solver);
        }
        solver.pop();
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
