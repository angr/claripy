/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"


/** Verify that the add function compiles and can be run without issue */
void add() {

    // Create input
    std::vector<Factory::Ptr<Expression::Base>> input {
        4,
        // Temporary so that it looses the reference after construction
        UnitTest::TestLib::Factories::t_literal<Expression::BV>()
    };

    const auto exp { Create::add(Create::EAnVec {}, std::move(input)) };

    // Pointer checks
    for (auto &i : input) {
        // Since input has 4 identical items
        UNITTEST_ASSERT(static_cast<Constants::UInt>(i.use_count()) == 2 * input.size())
    }
    UNITTEST_ASSERT(exp->op.use_count() == 1)

    // Type check
    const auto exp_bv { Utils::dynamic_down_cast_throw_on_fail<Expression::BV>(exp) };
    const auto i0_bv { Utils::dynamic_down_cast_throw_on_fail<Expression::BV>(input[0]) };
    const auto flat { Utils::dynamic_down_cast_throw_on_fail<Op::Add>(exp->op) };

    // Contains check
    UNITTEST_ASSERT(flat->operands.size() == input.size())
    for (Constants::UInt i = 0; i < input.size(); ++i) {
        UNITTEST_ASSERT(flat->operands[i] == input[i]);
    }

    // Size test
    UNITTEST_ASSERT(i0_bv->size == exp_bv->size)
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(add)
