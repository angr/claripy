/**
 * @file
 * \ingroup unittest
 */
#include "mode_binary.hpp"


/** Test the Create::FP::add function */
void add() {
    mode_binary<Op::FP::Add, Create::FP::add>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(add)
