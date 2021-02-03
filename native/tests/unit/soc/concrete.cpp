/**
 * @file
 * \ingroup unittest
 */
#include "soc.hpp"
#include "testlib.hpp"


/** Verify that the Concrete class works */
void concrete() {
    // Construct
    const auto c1 = SOC::factory<Concrete>();
    const auto c2 = SOC::factory<Concrete>();
    // Verify factory works
    UNITTEST_ASSERT(c1 == c2)
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(concrete)
