/**
 * @file
 * \ingroup unittest
 */
#include "binary.hpp"


/** Test the Create::concat function */
void concat() {
    binary<Expression::BV, Op::Concat, SM::Add, Create::concat<Expression::BV>>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(concat)
