/**
 * @file
 * \ingroup unittest
 */
#include "../dcast.hpp"

#include <testlib/testlib.hpp>


/** Create a BV using either name or val depending on Literal */
template <bool Literal> Expr::BasePtr create_bv(std::string name, const I64 val) {
    if constexpr (Literal) {
        return Create::literal(Util::unsign(val));
    }
    else {
        (void) val;
        return Create::symbol_bv(std::move(name), name.size() * CHAR_BIT);
    }
}

/** Test the sub_string create function */
template <bool Literal> void sub_string_b() {

    // Create distinct inputs
    const auto a { Create::literal(0_ui) };
    const U64 b_value { 1 };
    const auto b { create_bv<Literal>("named", b_value) };
    const auto c { Create::literal("2"s) };

    // Test
    const auto exp { Create::String::sub_string(a, b, c) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2);
    UNITTEST_ASSERT(b.use_count() == 2);
    UNITTEST_ASSERT(c.use_count() == 2);
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto ss_op { dcast<Op::String::SubString>(exp->op) };
    const auto exp_down { dcast<Expr::String>(exp) };
    const auto a_down { dcast<Expr::BV>(a) };
    const auto b_down { dcast<Expr::BV>(b) };
    const auto c_down { dcast<Expr::String>(c) };

    // Contains check
    UNITTEST_ASSERT(ss_op->start_index == a);
    UNITTEST_ASSERT(ss_op->count == b);
    UNITTEST_ASSERT(ss_op->full_string == c);

    // Size check
    if constexpr (Literal) {
        UNITTEST_ASSERT(exp_down->bit_length == CHAR_BIT * b_value);
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
