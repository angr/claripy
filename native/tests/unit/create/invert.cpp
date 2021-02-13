/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"


/** Verify that the invert function compiles and can be run without issue */
void invert() {

    // Create input
    const auto a { UnitTest::TestLib::Factories::t_literal<Expression::BV>() };
    const auto b { UnitTest::TestLib::Factories::t_literal<Expression::Bool>() };

    // Test
    (void) Create::invert<Expression::BV>(Create::EAnVec {}, a);
    (void) Create::invert<Expression::Bool>(Create::EAnVec {}, b);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(invert)
