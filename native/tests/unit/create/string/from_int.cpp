/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"

#include "../dcast.hpp"


/** Test the from_int create functions */
void from_int() {

    // For brevity
    namespace F = UnitTest::TestLib::Factories;
    namespace Ex = Expression;

    // Create input
    const auto a { F::t_literal<Ex::BV>(0) };

    // Test
    const auto exp { Create::String::from_int(a) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2);
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto op_down { dcast<Op::String::FromInt>(exp->op) };
    const auto exp_down { dcast<Ex::String>(exp) };
    const auto a_down { dcast<Ex::BV>(a) };

    // Contains check
    UNITTEST_ASSERT(op_down->child == a);

    // Size check
    UNITTEST_ASSERT(exp_down->bit_length == a_down->bit_length + 2_ui * 8);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(from_int)
