/**
 * @file
 * \ingroup unittest
 */
#include "../dcast.hpp"

#include <testlib/testlib.hpp>


/** Verify that the to_bv<Sgn> function compiles and can be run without issue */
template <bool Signed> void to_bv_b() {

    // Create distinct inputs
    const Mode::FP::Rounding mode { Mode::FP::Rounding::TowardsZero };
    const auto fp { Create::literal(0.) };
    const U64 bit_length { 16 };

    // Test
    const auto exp { (Signed ? Create::FP::to_bv_signed
                             : Create::FP::to_bv_unsigned)(mode, fp, bit_length, { nullptr }) };

    // Pointer checks
    UNITTEST_ASSERT(fp.use_count() == 2);
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    using To = std::conditional_t<Signed, Op::FP::ToBVSigned, Op::FP::ToBVUnsigned>;
    const auto op_down { dcast<To>(exp->op) };
    const auto exp_down { dcast<Expr::BV>(exp) };

    // Contains check
    UNITTEST_ASSERT(op_down->fp == fp);

    // Size check
    UNITTEST_ASSERT(exp_down->bit_length == bit_length);
}

/** Verify that the to_bv function compiles and can be run without issue */
void to_bv() {
    to_bv_b<true>();
    to_bv_b<false>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(to_bv)
