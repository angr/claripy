/**
 * @file
 * \ingroup unittest
 */
#include "unary.hpp"


/** Test the Create::abs function */
void abs() {
    unary<Expression::BV, Op::Abs, Create::abs<Expression::BV>>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(abs)
