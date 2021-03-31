/**
 * @file
 * \ingroup unittest
 */
#include "op.hpp"
#include "testlib.hpp"


/** Verify that the Eq class is constructible
 * @todo improve
 */
void eq() {
    const auto e = UnitTest::TestLib::Factories::t_literal();
    const auto op = Utils::static_down_cast<Op::Eq>(Op::factory<Op::Eq>(e, e));
    UNITTEST_ASSERT(op->left->hash == op->right->hash);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(eq)
