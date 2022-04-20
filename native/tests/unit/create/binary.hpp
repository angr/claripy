/**
 * @file
 * @brief Trivial binary create test
 * \ingroup unittest
 */
#ifndef R_TESTS_UNIT_CREATE_BINARY_HPP_
#define R_TESTS_UNIT_CREATE_BINARY_HPP_

#include "create.hpp"
#include "dcast.hpp"
#include "testlib.hpp"


/** SizeMode shortcut */
using SM = Create::Private::SizeMode;


/** Test a binary op */
template <typename Out, typename In, typename OpT, SM Mode, auto CreateF> inline void binary() {
    static_assert(Util::Type::Is::ancestor<Expr::Base, Out>, "binary requires Out be an Expr");
    static_assert(Util::Type::Is::ancestor<Expr::Base, In>, "binary requires In be an Expr");
    static_assert(Op::is_binary<OpT>, "binary requires a binary OpT");
    if constexpr (Util::Type::Is::ancestor<Expr::Bits, Out>) {
        const constexpr bool sized_in { Util::Type::Is::ancestor<Expr::Bits, In> };
        static_assert(Util::TD::boolean<sized_in, In>,
                      "binary does not support sized output types without sized input types");
    }

    // Create distinct inputs
    const auto a { UnitTest::TestLib::Factories::t_literal<In>(0) };
    const auto b { UnitTest::TestLib::Factories::t_literal<In>(1) };

    // Test
    const auto exp { CreateF(a, b, nullptr) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2);
    UNITTEST_ASSERT(a.use_count() == 2);
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
    if constexpr (Util::Type::Is::ancestor<Expr::Bits, Out>) {
        // Because of previous static asserts we know In must also be sized
        U64 new_bit_length { a_down->bit_length };
        if constexpr (Mode == SM::Add) {
            new_bit_length += b_down->bit_length;
        }
        else if constexpr (Mode != SM::First) {
            static_assert(Util::CD::false_<Mode>, "Unsupported mode for binary");
        }
        UNITTEST_ASSERT(exp_down->bit_length == new_bit_length);
    }
}

/** A specialization where In = Out */
template <typename InOut, typename OpT, SM Mode, auto CreateF> inline void binary() {
    binary<InOut, InOut, OpT, Mode, CreateF>();
}

#endif
