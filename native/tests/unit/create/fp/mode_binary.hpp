/**
 * @file
 * @brief Trivial binary create test
 * \ingroup unittest
 */
#ifndef R_UNIT_CREATE_FP_MODEBINARY_HPP_
#define R_UNIT_CREATE_FP_MODEBINARY_HPP_

#include "create.hpp"
#include "testlib.hpp"


/** Test a binary op */
template <typename OpT, auto CreateF> inline void mode_binary() {
    static_assert(Op::FP::is_mode_binary<OpT>, "mode_binary requires a mode_binary OpT");

    // Create distinct inputs
    const auto a { UnitTest::TestLib::Factories::t_literal<Expression::FP>(0) };
    const auto b { UnitTest::TestLib::Factories::t_literal<Expression::FP>(1) };

    // Test
    const Mode::FP mode { Mode::FP::TowardsZero };
    const auto exp { CreateF(a, b, mode, nullptr) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2);
    UNITTEST_ASSERT(b.use_count() == 2);
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto exp_down { Utils::dynamic_down_cast_throw_on_fail<Expression::FP>(exp) };
    const auto a_down { Utils::dynamic_down_cast_throw_on_fail<Expression::FP>(a) };
    const auto mbinary { Utils::dynamic_down_cast_throw_on_fail<OpT>(exp->op) };
    (void) Utils::dynamic_down_cast_throw_on_fail<Expression::FP>(b);

    // Contains check
    UNITTEST_ASSERT(mbinary->left == a);
    UNITTEST_ASSERT(mbinary->right == b);
    UNITTEST_ASSERT(mbinary->mode == mode);

    // Size test
    UNITTEST_ASSERT(exp_down->bit_length == a_down->bit_length);
}

#endif
