/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"


/** Verify that the add function compiles and can be run without issue */
void add() {

    // Create input
    const auto a { UnitTest::TestLib::Factories::t_literal<Expression::FP>() };
    const auto b { UnitTest::TestLib::Factories::t_literal<Expression::FP>() };

    (void) Create::FP::add(Create::EAnVec {}, a, b, Mode::FP::TowardsZero);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(add)
