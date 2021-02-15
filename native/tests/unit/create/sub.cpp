/**
 * @file
 * \ingroup unittest
 */
#include "binary.hpp"


/** Test the Create::sub function */
void sub() {
    binary<Expression::BV, Op::Sub, SM::First, Create::sub>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(sub)
