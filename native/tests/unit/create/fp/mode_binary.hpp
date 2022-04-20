/**
 * @file
 * @brief Trivial binary create test
 * \ingroup unittest
 */
#ifndef R_TESTS_UNIT_CREATE_FP_MODEBINARY_HPP_
#define R_TESTS_UNIT_CREATE_FP_MODEBINARY_HPP_

#include "create.hpp"
#include "testlib.hpp"

#include "../dcast.hpp"


/** Test a binary op */
template <typename OpT, auto CreateF> inline void mode_binary() {
    static_assert(Op::FP::is_mode_binary<OpT>, "mode_binary requires a mode_binary OpT");

    // Create distinct inputs
    const auto a { Create::literal(0.) };
    const auto b { Create::literal(1.) };

    // Test
    const Mode::FP::Rounding mode { Mode::FP::Rounding::TowardsZero };
    const auto exp { CreateF(a, b, mode, nullptr) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2);
    UNITTEST_ASSERT(b.use_count() == 2);
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto exp_down { dcast<Expr::FP>(exp) };
    const auto a_down { dcast<Expr::FP>(a) };
    const auto mbinary { dcast<OpT>(exp->op) };
    (void) dcast<Expr::FP>(b);

    // Contains check
    UNITTEST_ASSERT(mbinary->left == a);
    UNITTEST_ASSERT(mbinary->right == b);
    UNITTEST_ASSERT(mbinary->mode == mode);

    // Size test
    UNITTEST_ASSERT(exp_down->bit_length == a_down->bit_length);
}

#endif
