/**
 * @file
 * \ingroup unittest
 */
#include "exc.hpp"
#include "testlib.hpp"

/** Verify the BigInt API works */
void big_int() {
    const auto old_mode { exc(claricpp_big_int_mode_get()) };
    const auto got_mode { exc(claricpp_big_int_mode_set(ClaricppBimInt)) };
    const auto new_mode { exc(claricpp_big_int_mode_get()) };
    UNITTEST_ASSERT(old_mode == ClaricppBimStr); // This should be default
    UNITTEST_ASSERT(old_mode == got_mode);       // This should be default
    UNITTEST_ASSERT(new_mode == ClaricppBimInt); // This should be default
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(big_int)
