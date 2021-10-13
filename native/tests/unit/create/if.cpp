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
    namespace Ex = Expression; // NOLINT (false positive)

    // Create distinct inputs
    const auto a { F::t_literal<T>(0) };
    const auto b { F::t_literal<T>(1) };
    const auto cond { F::t_literal<Ex::Bool>(1) };

    // Note that if T = bool, b == c; both bools exist in the backend as well so increment counts
    const Constants::UInt offset { std::is_same_v<T, Ex::Bool> ? 1 : 0 };

    // Sanity checks
    UNITTEST_ASSERT(a.use_count() == 1 + offset);     // a + backend?
    UNITTEST_ASSERT(b.use_count() == 1 + 2 * offset); // b + c? + backend?
    UNITTEST_ASSERT(cond.use_count() == 2 + offset);  // b? + c + backend

    // Test
    const auto exp { Create::if_<T>(cond, a, b) };

    // Pointer checks
    UNITTEST_ASSERT(a.use_count() == 2 + offset);        // prev + new.a
    UNITTEST_ASSERT(b.use_count() == 2 + 3 * offset);    // prev + new.b + new.c?
    UNITTEST_ASSERT(cond.use_count() == 3 + 2 * offset); // prev + new.b? + new.c
    UNITTEST_ASSERT(exp->op.use_count() == 1);

    // Type check
    const auto op { dcast<Op::If>(exp->op) };
    const auto c_down { dcast<Ex::Bool>(cond) };
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
    namespace Ex = Expression;
    if_t<Ex::BV>();
    if_t<Ex::Bool>();
    if_t<Ex::String>();
    if_t<Ex::FP>();
    if_t<Ex::VS>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(if_)
