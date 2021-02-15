/**
 * @file
 * @brief Trivial unary create test
 * \ingroup unittest
 */
#ifndef __TESTS_UNIT_CREATE_UNARY_HPP__
#define __TESTS_UNIT_CREATE_UNARY_HPP__

#include "create.hpp"
#include "testlib.hpp"


/** Test a unary op */
template <typename T, typename OpT, auto CreateF> inline void unary() {

    // Create input
    const auto a { UnitTest::TestLib::Factories::t_literal<T>() };

    // Test
    const auto exp { CreateF(Create::EAnVec {}, a) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2)
    UNITTEST_ASSERT(exp->op.use_count() == 1)

    // Type check
    Utils::Log::critical(__LINE__);
    const auto exp_down { Utils::dynamic_down_cast_throw_on_fail<T>(exp) };
    Utils::Log::critical(__LINE__);
    const auto a_down { Utils::dynamic_down_cast_throw_on_fail<T>(a) };
    Utils::Log::critical(__LINE__);
    const auto unary { Utils::dynamic_down_cast_throw_on_fail<OpT>(exp->op) };
    Utils::Log::critical(__LINE__);

    // Contains check
    UNITTEST_ASSERT(unary->child == a)

    // Size test
    if constexpr (Utils::is_ancestor<Expression::Bits, T>) {
        UNITTEST_ASSERT(a_down->size == exp_down->size)
    }
}

#endif
