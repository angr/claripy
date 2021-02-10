/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"


/** Verify that the add function compiles and can be run without issue */
void add() {

    // Create input
    std::vector<Factory::Ptr<Expression::Base>> input;
    for (int i = 0; i < 4; ++i) { // NOLINT
        input.push_back(UnitTest::TestLib::Factories::t_literal<Expression::BV>());
    }

    (void) Create::add<Expression::BV>(std::move(input), Create::EAnVec {});
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(add)
