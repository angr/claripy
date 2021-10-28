/**
 * @file
 * \ingroup api
 */
#include "cpp.hpp"

ClaricppExpr claricpp_expr_make_like_annotations(const ClaricppExpr old, ClaricppSPAV spav) {
    auto ret { API::to_c(Expr::make_like(API::to_cpp(old), std::move(API::to_cpp(spav)))) };
    API::free(spav);
    return ret;
}

SIZE_T claricpp_expr_bit_length(const ClaricppExpr expr) {
    return Expr::get_bit_length(API::to_cpp(expr));
}
