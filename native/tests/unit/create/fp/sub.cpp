/**
 * @file
 * \ingroup unittest
 */
#include "mode_binary.hpp"


/** Test the Create::FP::sub function */
void sub() {
    mode_binary<Op::FP::Sub, Create::FP::sub>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(sub)
