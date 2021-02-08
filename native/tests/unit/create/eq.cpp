/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"


/** Verify that the eq function compiles */
void eq() {
    const auto a { UnitTest::TestLib::Factories::t_literal() };
    const auto b { UnitTest::TestLib::Factories::t_literal() };
    (void) Create::eq(a, b, Expression::Base::AnnotationVec {});
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(eq)
