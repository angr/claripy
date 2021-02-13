/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"


/** Verify that the reverse function compiles and can be run without issue */
void reverse() {

    // Create input
    const auto a { UnitTest::TestLib::Factories::t_literal<Expression::BV>() };

    // Test
    (void) Create::reverse(Create::EAnVec {}, a);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(reverse)
