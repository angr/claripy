/**
 * @file
 * \ingroup unittest
 */
#include "dcast.hpp"

#include <testlib/testlib.hpp>


/** Verify that the extract function compiles and can be run without issue */
void extract() {

    // Create distinct inputs
    const U64 high { 2 };
    const U64 low { 2 };
    const auto a { Create::literal(0_ui) };

    // Test
    const auto exp { Create::extract(high, low, a) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2);
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto op_down { dcast<Op::Extract>(exp->op) };
    const auto exp_down { dcast<Expr::BV>(exp) };
    const auto a_down { dcast<Expr::BV>(a) };

    // Contains check
    UNITTEST_ASSERT(op_down->from == a);

    // Size check
    UNITTEST_ASSERT(exp_down->bit_length == high + 1 - low);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(extract)
