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