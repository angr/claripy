/**
 * @file
 * \ingroup unittest
 */
#include "unary.hpp"


/** Test the Create::invert function */
void invert() {
    unary<Expression::BV, Op::Invert, Create::invert<Expression::BV>>();
    unary<Expression::Bool, Op::Invert, Create::invert<Expression::Bool>>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(invert)
