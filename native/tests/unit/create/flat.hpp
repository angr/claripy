/**
 * @file
 * @brief Trivial flat create test
 * \ingroup unittest
 */
#ifndef R_TESTS_UNIT_CREATE_FLAT_HPP_
#define R_TESTS_UNIT_CREATE_FLAT_HPP_

#include "create.hpp"
#include "dcast.hpp"
#include "testlib.hpp"


/** SizeMode shortcut */
using SM = Create::Private::SizeMode;


/** Test a flat op */
template <typename T, typename OpT, SM Mode, auto CreateF> inline void flat() {
    static_assert(Util::Type::Is::ancestor<Expr::Base, T>, "flat requires T be an Expr");
    static_assert(Op::is_flat<OpT>, "flat requires a flat OpT");

    // Create input
    std::vector<Expr::BasePtr> input {
        4,
        // Temporary so that it looses the reference after construction
        UnitTest::TestLib::Factories::t_literal<T>()
    };

    // Test
    const auto exp { CreateF(input, nullptr) };

    // Pointer checks
    for (auto &i : input) {
        // Since input has 4 identical items
        UNITTEST_ASSERT(Util::unsign(i.use_count()) == 2 * input.size());
    }
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto flat { dcast<OpT>(exp->op) };
    const auto exp_down { dcast<T>(exp) };

    // Contains check
    UNITTEST_ASSERT(flat->operands.size() == input.size());
    for (U64 i = 0; i < input.size(); ++i) {
        UNITTEST_ASSERT(flat->operands[i] == input[i]);
    }

    // Size test
    if constexpr (Util::Type::Is::ancestor<Expr::Bits, T>) {
        static_assert(Mode == Util::TD::id<SM::First>, "Unsupported mode for flat");
        const auto i0 { dcast<T>(flat->operands[0]) };
        UNITTEST_ASSERT(exp_down->bit_length == i0->bit_length);
    }
}

#endif
