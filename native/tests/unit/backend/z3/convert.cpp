/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "testlib.hpp"

#include "../../make_ite.hpp"


/** Try to convert a claricpp expression to z3 */
void convert() {
    auto z3 { Backend::Z3::Z3 {} };

    // Test with if (4 == (x * 3)) then "Hello" else y
    const auto ite { make_ite("Hello") };
    (void) z3.convert(ite.get()); // Verify this runs
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(convert)
