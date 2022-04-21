/**
 * @file
 * \ingroup unittest
 */
#include "shim_z3.hpp"

#include <testlib/testlib.hpp>


/** Try to abstract a claricpp expression from z3 */
void abstract() {
    z3::context ctx;
    UnitTest::Friend::ShimZ3 z3;
    const auto abs { z3.abstract(ctx.bool_val(true)) };
    UNITTEST_ASSERT(abs == Create::literal(true));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(abstract)
