#include "expr.h"

ClaricppExpr claricpp_expr_make_like_annotations(const ClaricppExpr old, ClaricppAnnotation ans) {
    return API::to_c(Expr::make_like(API::to_cpp(old), API::to_cpp(ans)));
}