/**
 * @file
 * \ingroup unittest
 */
#include "binary.hpp"


/** Test the Create::div function */
void div() {
    binary<Expression::BV, Op::Div, SM::First, Create::div>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(div)
