/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"


/** Verify that the mul function compiles and can be run without issue */
void mul() {

    // Create input
    std::vector<Factory::Ptr<Expression::Base>> input;
    for (int i = 0; i < 4; ++i) {                                                   // NOLINT
        input.push_back(UnitTest::TestLib::Factories::t_literal<Expression::BV>()); // NOLINT
    }

    (void) Create::mul(Create::EAnVec {}, std::move(input));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(mul)
