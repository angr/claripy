/**
 * @file
 * \ingroup unittest
 */
#include "soc.hpp"
#include "testlib.hpp"


/** Verify that the Symbolic class works */
void symbolic() {
    // Names
    std::string n1 { "name1" };
    std::string n2 { n1 };
    std::string n3 { "name2" };
    // Construct
    const auto s1 = SOC::factory<SOC::Symbolic>(std::move(n1));
    const auto s2 = SOC::factory<SOC::Symbolic>(std::move(n2));
    const auto s3 = SOC::factory<SOC::Symbolic>(std::move(n3));
    // Verify factory works
    UNITTEST_ASSERT(s1 == s2)
    UNITTEST_ASSERT(s1 != s3)
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(symbolic)
