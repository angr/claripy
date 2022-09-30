/**
 * @file
 * \ingroup unittest
 */
#include "../dcast.hpp"

#include <testlib/testlib.hpp>


/** Test the from_int create functions */
void from_int() {

    // Test
    const auto a { Create::literal(0_ui) };
    const auto exp { Create::String::from_int(a) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2);
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto op_down { dcast<Op::String::FromInt>(exp->op) };
    const auto exp_down { dcast<Expr::String>(exp) };
    const auto a_down { dcast<Expr::BV>(a) };

    // Contains check
    UNITTEST_ASSERT(op_down->child == a);

    // Size check
    UNITTEST_ASSERT(exp_down->bit_length == CHAR_BIT * 10000);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(from_int)
