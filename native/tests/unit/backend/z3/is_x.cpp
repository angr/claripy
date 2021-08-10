/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "testlib.hpp"


/** Test is_true and is_false */
void is_x() {
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

    // Test is_true
    UNITTEST_ASSERT(z3.is_true(true_));
    UNITTEST_ASSERT(!z3.is_true(false_));
    UNITTEST_ASSERT(!z3.is_true(maybe_true));
    UNITTEST_ASSERT(!z3.is_true(maybe_false));

    // Test is_false
    UNITTEST_ASSERT(!z3.is_false(true_));
    UNITTEST_ASSERT(z3.is_false(false_));
    UNITTEST_ASSERT(!z3.is_false(maybe_true));
    UNITTEST_ASSERT(!z3.is_false(maybe_false));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(is_x)