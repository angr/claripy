/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** Verify that the Concrete class works */
void literal() {
    // Construct
    const auto c1 = Op::factory<Op::Literal>(std::string { "hi", 2 });
    const auto c2 = Op::factory<Op::Literal>(std::string { "hi", 2 });
    // Verify factory works
    UNITTEST_ASSERT(c1 == c2);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(literal)
