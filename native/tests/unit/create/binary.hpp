/**
 * @file
 * @brief Trivial binary create test
 * \ingroup unittest
 */
#ifndef __TESTS_UNIT_CREATE_BINARY_HPP__
#define __TESTS_UNIT_CREATE_BINARY_HPP__

#include "create.hpp"
#include "dcast.hpp"
#include "testlib.hpp"


/** SizeMode shortcut */
using SM = Create::Private::SizeMode;


/** Test a binary op */
template <typename Out, typename In, typename OpT, SM Mode, auto CreateF> inline void binary() {
    static_assert(Utils::is_ancestor<Expression::Base, Out>,
                  "binary requires Out be an Expression");
    static_assert(Utils::is_ancestor<Expression::Base, In>, "binary requires In be an Expression");
    static_assert(Op::is_binary<OpT>, "binary requires a binary OpT");
    if constexpr (Utils::is_ancestor<Expression::Bits, Out>) {
        const constexpr bool sized_in { Utils::is_ancestor<Expression::Bits, In> };
        static_assert(Utils::TD::boolean<sized_in, In>,
                      "binary does not suppot sized output types without sized input types");
    }

    // Create distinct inputs
    const auto a { UnitTest::TestLib::Factories::t_literal<In>(0) };
    const auto b { UnitTest::TestLib::Factories::t_literal<In>(1) };

    // Test
    const auto exp { CreateF(Create::EAnVec {}, a, b) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2);
    UNITTEST_ASSERT(b.use_count() == 2);
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto binary { dcast<OpT>(exp->op) };
    const auto exp_down { dcast<Out>(exp) };
    const auto a_down { dcast<In>(a) };
    const auto b_down { dcast<In>(b) };

    // Contains check
    UNITTEST_ASSERT(binary->left == a);
    UNITTEST_ASSERT(binary->right == b);

    // Size test
    if constexpr (Utils::is_ancestor<Expression::Bits, Out>) {
        // Because of previous static asserts we know In must also be sized
        Constants::UInt new_bit_length { a_down->bit_length };
        if constexpr (Mode == SM::Add) {
            new_bit_length += b_down->bit_length;
        }
        else if constexpr (Mode != SM::First) {
            static_assert(Utils::TD::false_<Mode>, "Unsupported mode for binary");
        }
        UNITTEST_ASSERT(exp_down->bit_length == new_bit_length);
    }
}

/** A specialization where In = Out */
template <typename InOut, typename OpT, SM Mode, auto CreateF> inline void binary() {
    binary<InOut, InOut, OpT, Mode, CreateF>();
}

#endif
