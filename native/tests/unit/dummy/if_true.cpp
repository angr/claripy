/**
 * @file
 * \ingroup unittest
 */
#include "dummy.hpp"
#include "testlib.hpp"


/** Verify that the if_true class works */
void if_true() {
    const auto b = UnitTest::TestLib::Factories::t_literal<Expression::Bool>();

    Dummy::echo(true, true);
    UNITTEST_ASSERT(b->is_true())
    UNITTEST_ASSERT(!b->is_false())

    Dummy::echo(true, false);
    UNITTEST_ASSERT(!b->is_true())
    UNITTEST_ASSERT(b->is_false())
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(if_true)
