/**
 * @file
 * \ingroup unittest
 */
#include "shim_z3.hpp"

#include "../../make_ite.hpp"

#include <testlib/testlib.hpp>


/** Try to convert a claricpp expr to z3 */
void convert() {
    UnitTest::Friend::ShimZ3 z3;

    // Test with if (4 == (x * 3)) then "Hello" else y
    const auto ite { make_ite("Hello") };
    (void) z3.convert(ite.get()); // Verify this runs
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(convert)
