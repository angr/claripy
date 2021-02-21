/**
 * @file
 * @brief Trivial unary create test
 * \ingroup unittest
 */
#ifndef __TESTS_UNIT_CREATE_UNARY_HPP__
#define __TESTS_UNIT_CREATE_UNARY_HPP__

#include "create.hpp"
#include "dcast.hpp"
#include "testlib.hpp"


/** Test a unary op */
template <typename Out, typename In, typename OpT, auto CreateF> inline void unary() {
    static_assert(Utils::is_ancestor<Expression::Base, Out>,
                  "unary requires Out be an Expression");
    static_assert(Utils::is_ancestor<Expression::Base, In>, "unary requires In be an Expression");
    static_assert(Op::is_unary<OpT>, "unary requires a unary OpT");

    // Create input
    const auto a { UnitTest::TestLib::Factories::t_literal<In>() };

    // Test
    const auto exp { CreateF(Create::EAnVec {}, a) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2)
    UNITTEST_ASSERT(exp->op.use_count() == 1)

    // Type check
    const auto exp_down { dcast<Out>(exp) };
    const auto a_down { dcast<In>(a) };
    const auto unary { dcast<OpT>(exp->op) };

    // Contains check
    UNITTEST_ASSERT(unary->child == a)

    // Size test
    if constexpr (Utils::is_ancestor<Expression::Bits, Out>) {
        static_assert(Utils::TD::boolean<Utils::is_ancestor<Expression::Bits, In>, In>,
                      "unary requires a sized input type for a sized output type");
        UNITTEST_ASSERT(a_down->size == exp_down->size)
    }
}

/** Test a unary op
 *  A specialization where In = Out
 */
template <typename InOut, typename OpT, auto CreateF> inline void unary() {
    return unary<InOut, InOut, OpT, CreateF>();
}

#endif
