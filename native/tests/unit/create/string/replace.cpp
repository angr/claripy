/**
 * @file
 * \ingroup unittest
 */
#include "../dcast.hpp"

#include <testlib/testlib.hpp>


/** Test the replace create functions
 *  Note: this is not a trivial ternary test because the length
 *  calculation is done in a special way.
 */
void replace() {
    static_assert(Op::is_ternary<Op::String::Replace>, "ternary requires a ternary OpT");

    // Create distinct inputs
    const auto a { Create::literal("0"s) };
    const auto b { Create::literal("1"s) };
    const auto c { Create::literal("2"s) };

    // Test
    const auto exp { Create::String::replace(a, b, c) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2);
    UNITTEST_ASSERT(b.use_count() == 2);
    UNITTEST_ASSERT(c.use_count() == 2);
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto ternary { dcast<Op::String::Replace>(exp->op) };
    const auto exp_down { dcast<Expr::String>(exp) };
    const auto a_down { dcast<Expr::String>(a) };
    const auto b_down { dcast<Expr::String>(b) };
    const auto c_down { dcast<Expr::String>(c) };

    // Contains check
    UNITTEST_ASSERT(ternary->first == a);
    UNITTEST_ASSERT(ternary->second == b);
    UNITTEST_ASSERT(ternary->third == c);

    // Size check
    U64 new_bit_length { a_down->bit_length };
    if (b_down->bit_length < c_down->bit_length) {
        new_bit_length = new_bit_length - b_down->bit_length + c_down->bit_length;
    }
    UNITTEST_ASSERT(exp_down->bit_length == new_bit_length);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(replace)
