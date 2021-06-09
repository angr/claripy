/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"

#include "../dcast.hpp"


/** Verify that the from_fp function compiles and can be run without issue */
void from_fp() {

    // For brevity
    namespace F = UnitTest::TestLib::Factories;
    namespace Ex = Expression; // NOLINT (false positive)

    // Create distinct inputs
    const auto mode { Mode::FP::Rounding::TowardsZero };
    const auto fp { F::t_literal<Ex::FP>(0) };

    // Size check
    UNITTEST_ASSERT(dcast<Ex::FP>(fp)->bit_length == Mode::FP::dbl.width());

    // Test
    const auto exp { Create::FP::from_fp(mode, fp, Mode::FP::flt) };

    // Pointer checks
    UNITTEST_ASSERT(fp.use_count() == 2);
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto op_down { dcast<Op::FP::FromFP>(exp->op) };
    const auto exp_down { dcast<Ex::FP>(exp) };

    // Contains check
    UNITTEST_ASSERT(op_down->fp == fp);

    // Size check
    UNITTEST_ASSERT(exp_down->bit_length == Mode::FP::flt.width());
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(from_fp)
