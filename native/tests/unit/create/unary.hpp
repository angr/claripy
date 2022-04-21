/**
 * @file
 * @brief Trivial unary create test
 * \ingroup unittest
 */
#ifndef R_TESTS_UNIT_CREATE_UNARY_HPP_
#define R_TESTS_UNIT_CREATE_UNARY_HPP_

#include "dcast.hpp"

#include <testlib/testlib.hpp>


/** Test a unary op */
template <typename Out, typename In, typename OpT, auto CreateF> inline void unary() {
    static_assert(Util::Type::Is::ancestor<Expr::Base, Out>, "unary requires Out be an Expr");
    static_assert(Util::Type::Is::ancestor<Expr::Base, In>, "unary requires In be an Expr");
    static_assert(Op::is_unary<OpT>, "unary requires a unary OpT");

    // Create input
    const auto arg { UnitTest::TestLib::Factories::t_literal<In>() };

    // Test
    const auto exp { CreateF(arg, nullptr) };

    // Pointer checks
    UNITTEST_ASSERT(exp.use_count() == 1);
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto exp_down { dcast<Out>(exp) };
    const auto a_down { dcast<In>(arg) };
    const auto unary { dcast<OpT>(exp->op) };

    // Contains check
    UNITTEST_ASSERT(unary->child == arg);

    // Size test
    if constexpr (Util::Type::Is::ancestor<Expr::Bits, Out>) {
        static_assert(Util::TD::boolean<Util::Type::Is::ancestor<Expr::Bits, In>, In>,
                      "unary requires a sized input type for a sized output type");
        UNITTEST_ASSERT(a_down->bit_length == exp_down->bit_length)
    }
}

/** Test a unary op
 *  A specialization where In = Out
 */
template <typename InOut, typename OpT, auto CreateF> inline void unary() {
    return unary<InOut, InOut, OpT, CreateF>();
}

#endif
