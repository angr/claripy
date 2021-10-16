/**
 * @file
 * @brief Trivial flat create test
 * \ingroup unittest
 */
#ifndef R_UNIT_CREATE_FLAT_HPP_
#define R_UNIT_CREATE_FLAT_HPP_

#include "create.hpp"
#include "dcast.hpp"
#include "testlib.hpp"


/** SizeMode shortcut */
using SM = Create::Private::SizeMode;


/** Test a flat op */
template <typename T, typename OpT, SM Mode, auto CreateF> inline void flat() {
    static_assert(Utils::is_ancestor<Expression::Base, T>, "flat requires T be an Expression");
    static_assert(Op::is_flat<OpT>, "flat requires a flat OpT");

    // Create input
    std::vector<Factory::Ptr<Expression::Base>> input {
        4,
        // Temporary so that it looses the reference after construction
        UnitTest::TestLib::Factories::t_literal<T>()
    };

    // Test
    const auto exp { CreateF(std::move(input), nullptr) };

    // Pointer checks
    for (auto &i : input) {
        // Since input has 4 identical items
        UNITTEST_ASSERT(Utils::unsign(i.use_count()) == 2 * input.size());
    }
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto flat { dcast<OpT>(exp->op) };
    const auto exp_down { dcast<T>(exp) };

    // Contains check
    UNITTEST_ASSERT(flat->operands.size() == input.size());
    for (Constants::UInt i = 0; i < input.size(); ++i) {
        UNITTEST_ASSERT(flat->operands[i] == input[i]);
    }

    // Size test
    if constexpr (Utils::is_ancestor<Expression::Bits, T>) {
        static_assert(Mode == Utils::TD::id<SM::First>, "Unsupported mode for flat");
        const auto i0 { dcast<T>(flat->operands[0]) };
        UNITTEST_ASSERT(exp_down->bit_length == i0->bit_length);
    }
}

#endif
