/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** Test make_like */
void make_like() {
    namespace A = Annotation;
    using SA = A::SimplificationAvoidance;

    // Create an expr
    const auto e { Create::sub(Create::symbol_bv("bv", 64_ui), Create::literal(64_ui)) };

    // Create a few annotations
    auto ans { std::make_shared<A::Vec>(std::vector<A::BasePtr> {
        A::factory<A::Base>(),
        A::factory<SA>(),
    }) };

    // Make like
    const auto ml { Expr::make_like(e, std::move(ans)) };

    // Test
    UNITTEST_ASSERT(e->hash != ml->hash);
    UNITTEST_ASSERT(ml->annotations != nullptr);
    UNITTEST_ASSERT(ml->cuid == Expr::BV::static_cuid);

    UNITTEST_ASSERT(e->op->hash == ml->op->hash);
    UNITTEST_ASSERT(e->cuid == ml->cuid);
    UNITTEST_ASSERT(Expr::get_bit_length(e) == Expr::get_bit_length(ml));
    UNITTEST_ASSERT(e->symbolic == ml->symbolic);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(make_like)
