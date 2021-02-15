/**
 * @file
 * \ingroup unittest
 */
#include "flat.hpp"


/** Test the Create::mul function */
void mul() {
    flat<Expression::BV, Op::Mul, SM::First, Create::mul>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(mul)
