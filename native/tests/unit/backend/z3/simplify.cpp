/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "testlib.hpp"


/** Try to simplify a claricpp expression via z3 */
void simplify() {
    auto z3 { Backend::Z3::Z3 {} };
    namespace Ex = Expression;

    // Leaves
    const auto x { Create::symbol("x") };
    const auto y { Create::literal(true) };

    // Negations
    const auto not_x { Create::not_(x) };
    const auto not_y { Create::not_(y) };

    // Ors
    const auto c1 { Create::or_<Ex::Bool>({ x, not_y }) };
    const auto c2 { Create::or_<Ex::Bool>({ x, y }) };
    const auto c3 { Create::or_<Ex::Bool>({ not_x, y }) };

    // And
    const auto statement { Create::and_<Ex::Bool>({ c1, c2, c3 }) };

    // Simplify
    const auto simp { z3.simplify(statement) };

    // Solution
    const auto sol { x }; // x && y = x && true = x

    // Verify equality
    UNITTEST_ASSERT(Ex::inline_repr(simp) == Ex::inline_repr(sol));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(simplify)