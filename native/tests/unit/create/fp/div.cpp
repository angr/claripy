/**
 * @file
 * \ingroup unittest
 */
#include "mode_binary.hpp"


/** Test the Create::FP::div function */
void div() {
    mode_binary<Op::FP::Div, Create::FP::div>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(div)
