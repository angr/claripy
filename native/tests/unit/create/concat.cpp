/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"


/** Verify that the concat function compiles and can be run without issue */
void concat() {

    // Create input
    const auto a { UnitTest::TestLib::Factories::t_literal<Expression::BV>() };
    const auto b { UnitTest::TestLib::Factories::t_literal<Expression::BV>() };

    // Test
    (void) Create::concat<Expression::BV>(Create::EAnVec {}, a, b);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(concat)
