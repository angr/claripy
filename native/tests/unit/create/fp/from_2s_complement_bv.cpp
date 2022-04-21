/**
 * @file
 * \ingroup unittest
 */
#include "../dcast.hpp"

#include <testlib/testlib.hpp>


/** Verify that the from_2s_complement_bv function compiles and can be run without issue
 *  for the given value of Signed
 */
template <Mode::Signed Sgn> void from_2s_complement_bv_v() {

    // Create distinct inputs
    const auto mode { Mode::FP::Rounding::TowardsZero };
    const auto bv { Create::literal(0_ui) };

    // Size check
    UNITTEST_ASSERT_MSG(
        dcast<Expr::BV>(bv)->bit_length >= Mode::FP::dbl.width(),
        "This is not a test failure; but rather the test function itself needs to be fixed");

    // Test
    const auto exp { Create::FP::from_2s_complement_bv<Sgn>(mode, bv, Mode::FP::dbl, { nullptr }) };

    // Pointer checks
    UNITTEST_ASSERT(bv.use_count() == 2);
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto op_down { dcast<Op::FP::From2sComplementBV<Sgn>>(exp->op) };
    const auto exp_down { dcast<Expr::FP>(exp) };

    // Contains check
    UNITTEST_ASSERT(op_down->bv == bv);

    // Size check
    UNITTEST_ASSERT(exp_down->bit_length == Mode::FP::dbl.width());
}

/** Verify that the from_2s_complement_bv function compiles and can be run without issue */
void from_2s_complement_bv() {
    from_2s_complement_bv_v<Mode::Signed::Signed>();
    from_2s_complement_bv_v<Mode::Signed::Unsigned>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(from_2s_complement_bv)
