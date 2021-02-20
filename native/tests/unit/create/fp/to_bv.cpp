/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"


/** A dynamic down-cast alias */
template <typename T, typename U> auto dcast(const U &u) {
    return Utils::dynamic_down_cast_throw_on_fail<T>(u);
}

/** Verify that the to_bv<Signed> function compiles and can be run without issue */
template <bool Signed> void to_bv_b() {

    // For brevity
    namespace F = UnitTest::TestLib::Factories;
    namespace Ex = Expression;

    // Create distinct inputs
    const Mode::FP mode { Mode::FP::TowardsZero };
    const auto fp { F::t_literal<Ex::FP>(0) };
    const Constants::UInt bit_length { 16 };

    // Test
    const auto exp { Create::to_bv<Signed>(Create::EAnVec {}, mode, fp, bit_length) };

    // Pointer checks
    UNITTEST_ASSERT(fp.use_count() == 2)
    UNITTEST_ASSERT(exp->op.use_count() == 1)

    // Type check
    const auto op_down { dcast<Op::ToBV<Signed>>(exp->op) };
    const auto exp_down { dcast<Ex::BV>(exp) };

    // Contains check
    UNITTEST_ASSERT(op_down->fp == fp)

    // Size check
    UNITTEST_ASSERT(exp_down->size == bit_length)
}

/** Verify that the to_bv function compiles and can be run without issue */
void to_bv() {
    to_bv_b<true>();
    to_bv_b<false>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(to_bv)
