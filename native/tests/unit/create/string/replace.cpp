/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"

#include "../dcast.hpp"


/** Test the replace create functions */
void replace() {
    static_assert(Op::is_ternary<Op::String::Replace>, "ternary requires a ternary OpT");

    // For brevity
    namespace F = UnitTest::TestLib::Factories;
    using ES = Expression::String;
    namespace CS = Create::String;
    namespace OS = Op::String;

    // Create distinct inputs
    const auto a { F::t_literal<ES>(0) };
    const auto b { F::t_literal<ES>(1) };
    const auto c { F::t_literal<ES>(2) };

    // Test
    const auto exp { CS::replace(Create::EAnVec {}, a, b, c) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2)
    UNITTEST_ASSERT(b.use_count() == 2)
    UNITTEST_ASSERT(c.use_count() == 2)
    UNITTEST_ASSERT(exp->op.use_count() == 1)

    // Type check
    const auto ternary { dcast<OS::Replace>(exp->op) };
    const auto exp_down { dcast<ES>(exp) };
    const auto a_down { dcast<ES>(a) };
    const auto b_down { dcast<ES>(b) };
    const auto c_down { dcast<ES>(c) };

    // Contains check
    UNITTEST_ASSERT(ternary->first == a)
    UNITTEST_ASSERT(ternary->second == b)
    UNITTEST_ASSERT(ternary->third == c)

    // Size check
    Constants::UInt size { a_down->bit_length };
    if (b_down->bit_length < c_down->bit_length) {
        size = size - b_down->bit_length + c_down->bit_length;
    }
    UNITTEST_ASSERT(exp_down->bit_length == size)
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(replace)
