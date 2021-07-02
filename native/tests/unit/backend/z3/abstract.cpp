/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "testlib.hpp"


/** Try to abstract a claricpp expression from z3 */
void abstract() {
    z3::context ctx;
    auto z3 { Backend::Z3::Z3 {} };
    const auto abs { z3.abstract(ctx.bool_val(true)) };
    UNITTEST_ASSERT(abs == Create::literal(true));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(abstract)
