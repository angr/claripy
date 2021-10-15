/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include "../dcast.hpp"


/** Create a BV using either name or val depending on Literal */
template <bool Literal> Expression::BasePtr create_bv(std::string name, const Constants::Int val) {
    if constexpr (Literal) {
        return UnitTest::TestLib::Factories::t_literal<Expression::BV>(val);
    }
    else {
        (void) val;
        return Create::symbol<Expression::BV>(std::move(name), name.size() * BitLength::char_bit);
    }
}

/** Test the sub_string create function */
template <bool Literal> void sub_string_b() {

    // For brevity
    namespace F = UnitTest::TestLib::Factories;
    namespace CS = Create::String;
    namespace Ex = Expression; // NOLINT (false positive)
    namespace OS = Op::String; // NOLINT (false positive)

    // Create distinct inputs
    const auto a { F::t_literal<Expression::BV>(0) };
    const Ex::BasePtr b { create_bv<Literal>("named", 1) };
    const auto c { F::t_literal<Expression::String>(2) };

    // Test
    const auto exp { CS::sub_string(a, b, c) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2);
    UNITTEST_ASSERT(b.use_count() == 2);
    UNITTEST_ASSERT(c.use_count() == 2);
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto ss_op { dcast<OS::SubString>(exp->op) };
    const auto exp_down { dcast<Ex::String>(exp) };
    const auto a_down { dcast<Ex::BV>(a) };
    const auto b_down { dcast<Ex::BV>(b) };
    const auto c_down { dcast<Ex::String>(c) };

    // Contains check
    UNITTEST_ASSERT(ss_op->start_index == a);
    UNITTEST_ASSERT(ss_op->count == b);
    UNITTEST_ASSERT(ss_op->full_string == c);

    // Size check
    if constexpr (Literal) {
        UNITTEST_ASSERT(exp_down->bit_length == 0x1000); // TODO
    }
    else {
        UNITTEST_ASSERT(exp_down->bit_length == c_down->bit_length);
    }
}

void sub_string() {
    sub_string_b<true>();
    sub_string_b<false>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(sub_string)
