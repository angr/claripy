/**
 * @file
 * \ingroup unittest
 */
#include "../dcast.hpp"

#include <testlib/testlib.hpp>


/** Test the index_of create functions */
void index_of() {

    // For brevity
    namespace CS = Create::String;
    namespace OS = Op::String;

    // Create distinct inputs
    const auto a { Create::literal("0"s) };
    const auto b { Create::literal("1"s) };
    const auto c { Create::literal(2_ui) };
    const U64 bit_length { 16 };

    // Test
    const auto exp { CS::index_of(a, b, c, bit_length) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2);
    UNITTEST_ASSERT(b.use_count() == 2);
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto ido { dcast<OS::IndexOf>(exp->op) };
    const auto exp_down { dcast<Expr::BV>(exp) };
    const auto a_down { dcast<Expr::String>(a) };
    const auto b_down { dcast<Expr::String>(b) };

    // Contains check
    UNITTEST_ASSERT(ido->str == a);
    UNITTEST_ASSERT(ido->pattern == b);
    UNITTEST_ASSERT(ido->start_index == c);

    // Size check
    UNITTEST_ASSERT(exp_down->bit_length == bit_length);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(index_of)
