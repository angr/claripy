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
    auto e { Create::sub(Create::symbol<Expr::BV>("bv", 64), Create::literal(64_ui)) };
    auto e_copy { e };

    // Create a few annotations
    Annotation::SPAV ans { std::make_shared<A::Vec>(std::vector<A::BasePtr> {
        A::factory<A::Base>(),
        A::factory<SA>(),
    }) };

    // Make like
    const auto f { claricpp_expr_make_like_annotations };
    const auto ml_c { f(API::to_c(std::move(e_copy)), API::to_c(std::move(ans))) };
    const auto ml { API::to_cpp(ml_c) };

    // Test
    UNITTEST_ASSERT(e != nullptr);
    UNITTEST_ASSERT(ml != nullptr);

    UNITTEST_ASSERT(e->hash != ml->hash);
    UNITTEST_ASSERT(ml->annotations != nullptr);
    UNITTEST_ASSERT(ml->cuid == Expr::BV::static_cuid);

    UNITTEST_ASSERT(e->op->hash == ml->op->hash);
    UNITTEST_ASSERT(e->cuid == ml->cuid);
    UNITTEST_ASSERT(Expr::get_bit_length(e) == Expr::get_bit_length(ml));
    UNITTEST_ASSERT(e->symbolic == ml->symbolic);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(expr)
