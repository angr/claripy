/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** Verify the Expr API works */
void expr() {

    // Note: Below is full of memory leaks (this is a test so that's fine)
    // Because of it though there are multiple no lint statements

    namespace A = Annotation;
    using SA = A::SimplificationAvoidance;

    // Constants
    const auto bv_sym { Create::symbol<Expr::BV>("bv", 64) };
    const auto e { Create::sub(bv_sym, Create::literal(64_ui)) };
    const auto e_c { API::copy_to_c(e) };

    // Create a few annotations
    const auto ans { []() {
        return std::make_shared<const A::Vec>(
            std::vector<A::BasePtr> { A::factory<A::Base>(), A::factory<SA>() });
    } };

    // Make like
    const auto ml_c { claricpp_expr_make_like_annotations(e_c, API::to_c(ans())) }; // NOLINT
    const auto ml { API::to_cpp(ml_c) };

    // make like
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

    // bit length
    UNITTEST_ASSERT(claricpp_expr_bit_length(e_c) == e_len);

    // symbolic
    UNITTEST_ASSERT(claricpp_expr_symbolic(e_c));
    UNITTEST_ASSERT(!claricpp_expr_symbolic(API::copy_to_c(Create::literal(true)))); // NOLINT

    // annotations
    UNITTEST_ASSERT(claricpp_expr_annotations(e_c).ptr == nullptr); // NOLINT (leak ok)
    UNITTEST_ASSERT(API::to_cpp_ref(claricpp_expr_annotations(ml_c)).hash == ans()->hash);

    // args of zero extend
    const auto args { claricpp_expr_args(API::to_c(Create::zero_ext(bv_sym, 3))) }; // NOLINT
    UNITTEST_ASSERT(args.len == 2);
    UNITTEST_ASSERT(args.arr[0].type == ClaricppTypeEnumExpr);     // NOLINT (union ok)
    UNITTEST_ASSERT(API::to_cpp(args.arr[0].data.expr) == bv_sym); // NOLINT (union ok)
    UNITTEST_ASSERT(args.arr[1].type == ClaricppTypeEnumU64);      // NOLINT (union ok)
    UNITTEST_ASSERT(args.arr[1].data.prim.u64 == 3);               // NOLINT (union ok)

    // repr
    const std::string ml_c_repr { claricpp_expr_repr(ml_c) };
    const std::string ml_repr { ml->repr() };
    UNITTEST_ASSERT(ml_repr == ml_c_repr);

    // names
    UNITTEST_ASSERT(claricpp_expr_type_name(ml_c) == "BV"s);
    UNITTEST_ASSERT(claricpp_expr_op_name(ml_c) == "Sub"s);

    // CUIDs
    UNITTEST_ASSERT(claricpp_expr_cuid(ml_c) == ml->cuid);
    UNITTEST_ASSERT(claricpp_expr_op_cuid(ml_c) == ml->op->cuid);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(expr)
