/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "testlib.hpp"


/** Verify that the abs function compiles and can be run without issue */
void abs() {

    // Create input
    const auto a { UnitTest::TestLib::Factories::t_literal<Expression::BV>() };

    // Test
    const auto exp { Create::abs<Expression::BV>(Create::EAnVec {}, a) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2)
    UNITTEST_ASSERT(exp->op.use_count() == 1)

    // Type check
    const auto exp_bv { Utils::dynamic_down_cast_throw_on_fail<Expression::BV>(exp) };
    const auto a_bv { Utils::dynamic_down_cast_throw_on_fail<Expression::BV>(a) };
    const auto unary { Utils::dynamic_down_cast_throw_on_fail<Op::Abs>(exp->op) };

    // Contains check
    UNITTEST_ASSERT(unary->child == a)

    // Size test
    UNITTEST_ASSERT(a_bv->size == exp_bv->size)
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(abs)
