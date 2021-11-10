/**
 * @file
 * \ingroup api
 */
#include "cpp.hpp"

extern "C" {

    ClaricppExpr claricpp_expr_make_like_annotations(const ClaricppExpr old, ClaricppSPAV spav) {
        auto ret { API::to_c(Expr::make_like(API::to_cpp(old), std::move(API::to_cpp(spav)))) };
        API::free(spav);
        return ret;
    }

    SIZE_T claricpp_expr_bit_length(const ClaricppExpr expr) {
        return Expr::get_bit_length(API::to_cpp(expr));
    }

    ARRAY_OUT(ClaricppArg) claricpp_expr_args(const ClaricppExpr expr) {
        const auto &op { API::to_cpp_ref(expr).op };
        UTIL_AFFIRM_NOT_NULL_DEBUG(op);
        std::vector<Op::ArgVar> ret;
        op->python_children(ret);
        return API::to_arr(std::move(ret));
    }
}
