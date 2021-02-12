/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"


/** Verify that the neg function compiles and can be run without issue */
void neg() {

    // Create input
    const auto a { UnitTest::TestLib::Factories::t_literal<Expression::BV>() };

    // Test
    (void) Create::neg<Expression::BV>(Create::EAnVec {}, a);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(neg)
