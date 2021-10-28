/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** Verify the Expr API works */
void expr() {
    namespace A = Annotation;
    using SA = A::SimplificationAvoidance;

    // Create an expr
    const auto e { Create::sub(Create::symbol<Expr::BV>("bv", 64), Create::literal(64_ui)) };

    // Create a few annotations
    Annotation::SPAV ans { std::make_shared<A::Vec>(std::vector<A::BasePtr> {
        A::factory<A::Base>(),
        A::factory<SA>(),
    }) };

    // Make like
    const auto f { claricpp_expr_make_like_annotations };
    const auto ml_c { f(API::copy_to_c(e_copy), API::to_c(std::move(ans))) };
    const auto ml { API::to_cpp(ml_c) };

    // Test make like
    UNITTEST_ASSERT(e != nullptr);
    UNITTEST_ASSERT(ml != nullptr);

    UNITTEST_ASSERT(e->hash != ml->hash);
    UNITTEST_ASSERT(ml->annotations != nullptr);
    UNITTEST_ASSERT(ml->cuid == Expr::BV::static_cuid);

    const auto e_len { Expr::get_bit_length(e) };
    UNITTEST_ASSERT(e->op->hash == ml->op->hash);
    UNITTEST_ASSERT(e->cuid == ml->cuid);
    UNITTEST_ASSERT(e_len == Expr::get_bit_length(ml));
    UNITTEST_ASSERT(e->symbolic == ml->symbolic);

    // Test bit length
    UNITTEST_ASSERT(claricpp_expr_bit_length(API::copy_to_c(e)) == e_len);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(expr)
