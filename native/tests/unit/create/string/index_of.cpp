/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"

#include "../dcast.hpp"


/** Test the index_of create functions */
void index_of() {

    // For brevity
    namespace F = UnitTest::TestLib::Factories;
    namespace CS = Create::String;
    namespace Ex = Expression;
    namespace OS = Op::String;

    // Create distinct inputs
    const auto a { F::t_literal<Expression::String>(0) };
    const auto b { F::t_literal<Expression::String>(1) };
    const Constants::UInt start_index { 0 };
    const Constants::UInt bit_length { 16 };

    // Test
    const auto exp { CS::index_of(Create::EAnVec {}, a, b, start_index, bit_length) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2);
    UNITTEST_ASSERT(b.use_count() == 2);
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto ido { dcast<OS::IndexOf>(exp->op) };
    const auto exp_down { dcast<Ex::BV>(exp) };
    const auto a_down { dcast<Ex::String>(a) };
    const auto b_down { dcast<Ex::String>(b) };

    // Contains check
    UNITTEST_ASSERT(ido->str == a);
    UNITTEST_ASSERT(ido->pattern == b);
    UNITTEST_ASSERT(ido->start_index == start_index);

    // Size check
    UNITTEST_ASSERT(exp_down->bit_length == bit_length);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(index_of)
