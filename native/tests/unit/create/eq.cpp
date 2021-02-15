/**
 * @file
 * \ingroup unittest
 */
#include "binary.hpp"


/** Test the Create::eq function */
void eq() {
    binary<Expression::Bool, Op::Eq, SM::First, Create::eq<Expression::Bool>>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(eq)
