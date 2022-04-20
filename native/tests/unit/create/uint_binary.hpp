/**
 * @file
 * @brief Trivial int_int_binary create test
 * \ingroup unittest
 */
#ifndef R_TESTS_UNIT_CREATE_UINTBINARY_HPP_
#define R_TESTS_UNIT_CREATE_UINTBINARY_HPP_

#include "create.hpp"
#include "dcast.hpp"
#include "testlib.hpp"


/** SizeMode shortcut */
using SM = Create::Private::SizeMode;


/** Test an int uint_binary op */
template <typename Out, typename In, typename OpT, SM Mode, auto CreateF, typename IntT = U64>
inline void uint_binary() {
    static_assert(Util::Type::Is::ancestor<Expr::Base, Out>, "uint_binary requires Out be an Expr");
    static_assert(Util::Type::Is::ancestor<Expr::Base, In>, "uint_binary requires In be an Expr");
    static_assert(Op::is_uint_binary<OpT>, "uint_binary requires a uint_binary OpT");
    if constexpr (Util::Type::Is::ancestor<Expr::Bits, Out>) {
        const constexpr bool sized_in { Util::Type::Is::ancestor<Expr::Bits, In> };
        static_assert(Util::TD::boolean<sized_in, In>,
                      "uint_binary does not support sized output types without sized input types");
    }

    // Create inputs
    const auto a { UnitTest::TestLib::Factories::t_literal<In>(0) };
    const IntT b { 16 };

    // Test
    const auto exp { CreateF(a, b, nullptr) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2);
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto uint_binary { dcast<OpT>(exp->op) };
    const auto exp_down { dcast<Out>(exp) };
    const auto a_down { dcast<In>(a) };

    // Contains check
    UNITTEST_ASSERT(uint_binary->expr == a);
    UNITTEST_ASSERT(uint_binary->integer == b);

    // Size test
    if constexpr (Util::Type::Is::ancestor<Expr::Bits, Out>) {
        U64 new_bit_length { uint_binary->integer };
        if constexpr (Mode == SM::Add) {
            new_bit_length += a_down->bit_length;
        }
        else if constexpr (Mode != SM::Second) {
            static_assert(Util::TD::false_<Out>, "uint_binary does not support the given SizeMode");
        }
        UNITTEST_ASSERT(exp_down->bit_length == new_bit_length);
    }
}

/** Test an int uint_binary op
 *  A specialization where In = Out
 */
template <typename InOut, typename OpT, SM Mode, auto CreateF, typename IntT = U64>
inline void uint_binary() {
    uint_binary<InOut, InOut, OpT, Mode, CreateF, IntT>();
}

#endif
