/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"


/** Verify that the sub function compiles and can be run without issue */
void sub() {
    const auto a { UnitTest::TestLib::Factories::t_literal<Expression::BV>() };
    const auto b { UnitTest::TestLib::Factories::t_literal<Expression::BV>() };
    (void) Create::sub(Create::EAnVec {}, a, b);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(sub)
