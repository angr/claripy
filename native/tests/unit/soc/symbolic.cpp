/**
 * @file
 * \ingroup unittest
 */
#include "soc.hpp"
#include "testlib.hpp"


/** Verify that the Symbolic class works */
void symbolic() {
    // Construct
    const auto s1 = SOC::factory<Symbolic>("name1"s);
    const auto s2 = SOC::factory<Symbolic>("name1"s);
    const auto s3 = SOC::factory<Symbolic>("name3"s);
    // Verify factory works
    UNITTEST_ASSERT(s1 == s2)
    UNITTEST_ASSERT(s1 != s3)
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(symbolic)
