/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** Verify that the Eq class is constructible
 * @todo improve
 */
void eq() {
    const auto e { Create::literal(true) };
    const auto op { Util::PCast::Static::down<Op::Eq>(Op::factory<Op::Eq>(e, e)) };
    UNITTEST_ASSERT(op->left->hash == op->right->hash);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(eq)
