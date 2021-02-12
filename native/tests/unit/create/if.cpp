/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"


/** Verify that the if_ function compiles and can be run without issue */
void if_() {

    // Create input
    const auto a { UnitTest::TestLib::Factories::t_literal<Expression::BV>() };
    const auto b { UnitTest::TestLib::Factories::t_literal<Expression::BV>() };
    const auto c { UnitTest::TestLib::Factories::t_literal<Expression::Bool>() };

    (void) Create::if_<Expression::BV>(Create::EAnVec {}, c, a, b);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(if_)
