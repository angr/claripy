/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"


/** Verify that the eq function compiles and can be run without issue */
void eq() {
    const auto a { UnitTest::TestLib::Factories::t_literal<Expression::Bool>() };
    const auto b { UnitTest::TestLib::Factories::t_literal<Expression::Bool>() };
    (void) Create::eq<Expression::Bool>(Create::EAnVec {}, a, b);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(eq)
