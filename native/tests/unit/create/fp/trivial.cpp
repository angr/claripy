/**
 * @file
 * \ingroup unittest
 */
#include "mode_binary.hpp"


/** Test the trivial create fp functions */
void trivial() {

    // ModeBinary

    mode_binary<Op::FP::Add, Create::FP::add>();

    mode_binary<Op::FP::Sub, Create::FP::sub>();

    mode_binary<Op::FP::Div, Create::FP::div>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(trivial)
