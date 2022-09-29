/**
 * @file
 * \ingroup unittest
 */
#include "../dcast.hpp"

#include <testlib/testlib.hpp>


/** Verify that the from_2s_complement_bv function compiles and can be run without issue
 *  for the given value of Signed
 */
template <bool Signed> void from_2s_complement_bv_v() {

    // Create distinct inputs
    const auto mode { Mode::FP::Rounding::TowardsZero };
    const auto bv { Create::literal(0_ui) };

    // Size check
    UNITTEST_ASSERT_MSG(
        dcast<Expr::BV>(bv)->bit_length >= Mode::FP::dbl.width(),
        "This is not a test failure; but rather the test function itself needs to be fixed");

    // Test
    const auto exp { (Signed ? Create::FP::from_2s_complement_bv_signed
                             : Create::FP::from_2s_complement_bv_unsigned)(mode, bv, Mode::FP::dbl,
                                                                           {}) };

    // Pointer checks
    UNITTEST_ASSERT(bv.use_count() == 2);
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    using To = std::conditional_t<Signed, Op::FP::From2sComplementBVSigned,
                                  Op::FP::From2sComplementBVUnsigned>;
    const auto op_down { dcast<To>(exp->op) };
    const auto exp_down { dcast<Expr::FP>(exp) };

    // Contains check
    UNITTEST_ASSERT(op_down->bv == bv);

    // Size check
    UNITTEST_ASSERT(exp_down->bit_length == Mode::FP::dbl.width());
}

/** Verify that the from_2s_complement_bv function compiles and can be run without issue */
void from_2s_complement_bv() {
    from_2s_complement_bv_v<true>();
    from_2s_complement_bv_v<false>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(from_2s_complement_bv)
