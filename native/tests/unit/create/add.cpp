/**
 * @file
 * \ingroup unittest
 */
#include "flat.hpp"


/** Test the Create::add function */
void add() {
    flat<Expression::BV, Op::Add, SM::First, Create::add>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(add)
