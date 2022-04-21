/**
 * @file
 * \ingroup unittest
 */
#include "dcast.hpp"

#include <testlib/testlib.hpp>


/** Verify that the if_<T> function works */
template <typename T> void if_t() {
    namespace F = UnitTest::TestLib::Factories;

    // Create distinct inputs
    const auto a { F::t_literal<T>(0) };
    const auto b { F::t_literal<T>(1) };
    const auto cond { Create::literal(true) };

    // Gather stats
    const long offset { std::is_same_v<T, Expr::Bool> ? 1 : 0 };
    UNITTEST_ASSERT(a.use_count() == 1);
    UNITTEST_ASSERT(b.use_count() == 1 + offset);
    UNITTEST_ASSERT(cond.use_count() == 1 + offset);

    // Test
    const auto exp { Create::if_(cond, a, b) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2);
    UNITTEST_ASSERT(b.use_count() == 2 * (1 + offset));
    UNITTEST_ASSERT(cond.use_count() == 2 * (1 + offset));
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto op { dcast<Op::If>(exp->op) };
    const auto c_down { dcast<Expr::Bool>(cond) };
    const auto a_down { dcast<T>(a) };
    const auto b_down { dcast<T>(b) };
    (void) dcast<T>(exp);

    // Contains check
    UNITTEST_ASSERT(op->cond == cond);
    UNITTEST_ASSERT(op->if_true == a);
    UNITTEST_ASSERT(op->if_false == b);
}

/** Verify that the if_ function works */
void if_() {
    if_t<Expr::BV>();
    if_t<Expr::Bool>();
    if_t<Expr::String>();
    if_t<Expr::FP>();
    if_t<Expr::VS>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(if_)
