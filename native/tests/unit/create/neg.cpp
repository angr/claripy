/**
 * @file
 * \ingroup unittest
 */
#include "unary.hpp"


/** Test the Create::neg function */
void neg() {
    unary<Expression::BV, Op::Neg, Create::neg<Expression::BV>>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(neg)
