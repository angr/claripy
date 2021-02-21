/**
 * @file
 * \ingroup unittest
 */
#include "create.hpp"
#include "dcast.hpp"
#include "testlib.hpp"


/** Verify that the if_<T> function works */
template <typename T> void if_t() {

    // For brevity
    namespace F = UnitTest::TestLib::Factories;
    namespace Ex = Expression;

    // Create distinct inputs
    const auto a { F::t_literal<T>(0) };
    const auto b { F::t_literal<T>(1) };
    const auto c { F::t_literal<Ex::Bool>(2) };

    // Test
    const auto exp { Create::if_<T>(Create::EAnVec {}, c, a, b) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2)
    UNITTEST_ASSERT(b.use_count() == 2)
    UNITTEST_ASSERT(c.use_count() == 2)
    UNITTEST_ASSERT(exp->op.use_count() == 1)

    // Type check
    const auto op { dcast<Op::If>(exp->op) };
    const auto c_down { dcast<Ex::Bool>(c) };
    const auto a_down { dcast<T>(a) };
    const auto b_down { dcast<T>(b) };
    (void) dcast<T>(exp);

    // Contains check
    UNITTEST_ASSERT(op->cond == c)
    UNITTEST_ASSERT(op->if_true == a)
    UNITTEST_ASSERT(op->if_false == b)
}

/** Verify that the if_ function works */
void if_() {
    namespace Ex = Expression;
    if_t<Ex::BV>();
    if_t<Ex::Bool>();
    if_t<Ex::String>();
    if_t<Ex::FP>();
    if_t<Ex::VS>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(if_)
