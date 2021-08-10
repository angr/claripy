/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "testlib.hpp"


/** Test is_true and is_false */
void satisfiable() {
#if 0
    auto z3 { Backend::Z3::Z3 {} };
    using B = Expression::Bool;

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
    z3

    // Test sat
    UNITTEST_ASSERT(z3.satisfiable(true_));
    UNITTEST_ASSERT(!z3.satisfiable(false_));
    UNITTEST_ASSERT(z3.satisfiable(maybe_true));
    UNITTEST_ASSERT(z3.satisfiable(maybe_false));

    // Test sat with extra constraints
    auto ec = lambda[](const Expression::BasePtr& w) {
        std::set<Expression::BasePtr> ret;
        ret.emplace(Create::eq<B>(x, w));
        return ret;
    }
    UNITTEST_ASSERT(!z3.satisfiable(true_, ec(f)));
    UNITTEST_ASSERT(!z3.satisfiable(false_, ec(f)));
    UNITTEST_ASSERT(!z3.satisfiable(maybe_true, ec(f)));
    UNITTEST_ASSERT(z3.satisfiable(maybe_false, ec(t)));
#endif
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(satisfiable)