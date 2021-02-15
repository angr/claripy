/**
 * @file
 * @brief Trivial binary create test
 * \ingroup unittest
 */
#ifndef __TESTS_UNIT_CREATE_BINARY_HPP__
#define __TESTS_UNIT_CREATE_BINARY_HPP__

#include "create.hpp"
#include "testlib.hpp"


/** SizeMode shortcut */
using SM = Create::Private::SizeMode;


/** Test a binary op */
template <typename T, typename OpT, SM Mode, auto CreateF> inline void binary() {
    static_assert(Utils::is_ancestor<Expression::Base, T>, "binary requires T be an Expression");
    static_assert(Op::is_binary<OpT>, "binary requires a binary OpT");

    // Create distinct inputs
    const auto a { UnitTest::TestLib::Factories::t_literal<T>(0) };
    const auto b { UnitTest::TestLib::Factories::t_literal<T>(1) };

    // Test
    const auto exp { CreateF(Create::EAnVec {}, a, b) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2)
    UNITTEST_ASSERT(b.use_count() == 2)
    UNITTEST_ASSERT(exp->op.use_count() == 1)

    // Type check
    const auto binary { Utils::dynamic_down_cast_throw_on_fail<OpT>(exp->op) };
    const auto exp_down { Utils::dynamic_down_cast_throw_on_fail<T>(exp) };
    const auto a_down { Utils::dynamic_down_cast_throw_on_fail<T>(a) };
    const auto b_down { Utils::dynamic_down_cast_throw_on_fail<T>(b) };

    // Contains check
    UNITTEST_ASSERT(binary->left == a)
    UNITTEST_ASSERT(binary->right == b)

    // Size test
    if constexpr (Utils::is_ancestor<Expression::Bits, T>) {
        Constants::UInt size { a_down->size };
        if constexpr (Mode == SM::Add) {
            size += b_down->size;
        }
        else if constexpr (Mode != SM::First) {
            static_assert(Utils::TD::false_<Mode>, "Unsupported mode for binary");
        }
        UNITTEST_ASSERT(exp_down->size == size)
    }
}

#endif
