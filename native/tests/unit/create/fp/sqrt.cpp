/**
* @file
* \ingroup unittest
*/
#include "../dcast.hpp"

#include <testlib/testlib.hpp>


/** Verify that the sqrt function compiles and can be run without issue */
void sqrt() {

    // Create distinct inputs
    const Mode::FP::Rounding mode { Mode::FP::Rounding::TowardsZero };
    const auto fp { Create::literal(0.) };

    // Test
    const auto sq { Create::FP::sqrt(mode, fp) };

    // Pointer checks
    UNITTEST_ASSERT(fp.use_count() == 2);
    UNITTEST_ASSERT(sq->op.use_count() == 1);

    // Type check
    const auto op_down { dcast<Op::FP::Sqrt>(sq->op) };
    const auto exp_down { dcast<Expr::FP>(sq) };

    // Contains check
    UNITTEST_ASSERT(op_down->fp == fp);

    // Size check
    UNITTEST_ASSERT(exp_down->bit_length == Expr::bit_length(fp));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(sqrt)
