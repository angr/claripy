/**
 * @file
 * @brief Trivial int_int_binary create test
 * \ingroup unittest
 */
#ifndef __TESTS_UNIT_CREATE_INTint_binary_HPP__
#define __TESTS_UNIT_CREATE_INTint_binary_HPP__

#include "create.hpp"
#include "testlib.hpp"


/** SizeMode shortcut */
using SM = Create::Private::SizeMode;


/** Test an int int_binary op */
template <typename Out, typename In, typename OpT, SM Mode, auto CreateF, typename IntT>
inline void int_binary() {
    static_assert(Utils::is_ancestor<Expression::Base, Out>,
                  "int_binary requires Out be an Expression");
    static_assert(Utils::is_ancestor<Expression::Base, In>,
                  "int_binary requires In be an Expression");
    static_assert(Op::is_int_binary<OpT>, "int_binary requires a int_binary OpT");
    if constexpr (Utils::is_ancestor<Expression::Bits, Out>) {
        const constexpr bool sized_in { Utils::is_ancestor<Expression::Bits, In> };
        static_assert(Utils::TD::boolean<sized_in, In>,
                      "int_binary does not suppot sized output types without sized input types");
    }

    // Create inputs
    const auto a { UnitTest::TestLib::Factories::t_literal<In>(0) };
    const IntT b { 16 };

    // Test
    const auto exp { CreateF(Create::EAnVec {}, a, b) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2)
    UNITTEST_ASSERT(exp->op.use_count() == 1)

    // Type check
    const auto int_binary { Utils::dynamic_down_cast_throw_on_fail<OpT>(exp->op) };
    const auto exp_down { Utils::dynamic_down_cast_throw_on_fail<Out>(exp) };
    const auto a_down { Utils::dynamic_down_cast_throw_on_fail<In>(a) };

    // Contains check
    UNITTEST_ASSERT(int_binary->expr == a)
    UNITTEST_ASSERT(int_binary->integer == b)

    // Size test
    if constexpr (Utils::is_ancestor<Expression::Bits, Out>) {
        Constants::UInt esize { int_binary->integer };
        if constexpr (Mode == SM::Add) {
            esize += exp_down->size;
        }
        else if constexpr (Mode != SM::Second) {
            static_assert(Utils::TD::false_<Out>,
                          "int_binary does not support the given SizeMode");
        }
        UNITTEST_ASSERT(exp_down->size == esize)
    }
}

/** A specialization where In = Out
 *  Default IntT to Constants::UInt
 */
template <typename InOut, typename OpT, SM Mode, auto CreateF, typename IntT = Constants::UInt>
inline void int_binary() {
    int_binary<InOut, InOut, OpT, Mode, CreateF, IntT>();
}

#endif
