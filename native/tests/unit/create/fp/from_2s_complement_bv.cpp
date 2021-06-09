/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"

#include "../dcast.hpp"


/** Verify that the from_2s_complement_bv function compiles and can be run without issue
 *  for the given value of Signed
 */
template <bool Signed> void from_2s_complement_bv_v() {

    // For brevity
    namespace F = UnitTest::TestLib::Factories;
    namespace Ex = Expression; // NOLINT (false positive)

    // Create distinct inputs
    const auto mode { Mode::FP::Rounding::TowardsZero };
    const auto bv { F::t_literal<Ex::BV>(0) };

    // Size check
    UNITTEST_ASSERT_MSG(
        dcast<Ex::BV>(bv)->bit_length >= Mode::FP::dbl.width(),
        "This is not a test failure; but rather the test function itself needs to be fixed");

    // Test
    const auto exp { Create::FP::from_2s_complement<Signed>(mode, bv, Mode::FP::dbl) };

    // Pointer checks
    UNITTEST_ASSERT(bv.use_count() == 2);
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto op_down { dcast<Op::FP::From2sComplementBV<Signed>>(exp->op) };
    const auto exp_down { dcast<Ex::FP>(exp) };

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
