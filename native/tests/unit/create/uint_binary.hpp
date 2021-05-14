/**
 * @file
 * @brief Trivial int_int_binary create test
 * \ingroup unittest
 */
#ifndef R_UNIT_CREATE_UINTBINARY_HPP_
#define R_UNIT_CREATE_UINTBINARY_HPP_

#include "create.hpp"
#include "testlib.hpp"


/** SizeMode shortcut */
using SM = Create::Private::SizeMode;


/** Test an int uint_binary op */
template <typename Out, typename In, typename OpT, SM Mode, auto CreateF,
          typename IntT = Constants::UInt>
inline void uint_binary() {
    static_assert(Utils::is_ancestor<Expression::Base, Out>,
                  "uint_binary requires Out be an Expression");
    static_assert(Utils::is_ancestor<Expression::Base, In>,
                  "uint_binary requires In be an Expression");
    static_assert(Op::is_uint_binary<OpT>, "uint_binary requires a uint_binary OpT");
    if constexpr (Utils::is_ancestor<Expression::Bits, Out>) {
        const constexpr bool sized_in { Utils::is_ancestor<Expression::Bits, In> };
        static_assert(Utils::TD::boolean<sized_in, In>,
                      "uint_binary does not suppot sized output types without sized input types");
    }

    // Create inputs
    const auto a { UnitTest::TestLib::Factories::t_literal<In>(0) };
    const IntT b { 16 };

    // Test
    const auto exp { CreateF(Create::EAnVec {}, a, b) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2);
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto uint_binary { Utils::dynamic_down_cast_throw_on_fail<OpT>(exp->op) };
    const auto exp_down { Utils::dynamic_down_cast_throw_on_fail<Out>(exp) };
    const auto a_down { Utils::dynamic_down_cast_throw_on_fail<In>(a) };

    // Contains check
    UNITTEST_ASSERT(uint_binary->expr == a);
    UNITTEST_ASSERT(uint_binary->integer == b);

    // Size test
    if constexpr (Utils::is_ancestor<Expression::Bits, Out>) {
        Constants::UInt new_bit_length { uint_binary->integer };
        if constexpr (Mode == SM::Add) {
            new_bit_length += a_down->bit_length;
        }
        else if constexpr (Mode != SM::Second) {
            static_assert(Utils::TD::false_<Out>,
                          "uint_binary does not support the given SizeMode");
        }
        UNITTEST_ASSERT(exp_down->bit_length == new_bit_length);
    }
}

/** Test an int uint_binary op
 *  A specialization where In = Out
 */
template <typename InOut, typename OpT, SM Mode, auto CreateF, typename IntT = Constants::UInt>
inline void uint_binary() {
    uint_binary<InOut, InOut, OpT, Mode, CreateF, IntT>();
}

#endif
