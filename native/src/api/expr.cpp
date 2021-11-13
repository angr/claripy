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

    bool claricpp_expr_symbolic(const ClaricppExpr expr) { return API::to_cpp_ref(expr).symbolic; }

    ClaricppSPAV claricpp_expr_annotations(const ClaricppExpr expr) {
        const auto &ret { API::to_cpp_ref(expr).annotations };
        if (LIKELY(ret == nullptr)) {
            return {};
        }
        return API::copy_to_c(ret); // Can't move a reference to a const object
    }

    ARRAY_OUT(ClaricppArg) claricpp_expr_args(const ClaricppExpr expr) {
        const auto &op { API::to_cpp_ref(expr).op };
        UTIL_AFFIRM_NOT_NULL_DEBUG(op);
        std::vector<Op::ArgVar> ret;
        op->python_children(ret);
        return API::to_arr(std::move(ret));
    }

    const char *claricpp_expr_repr(const ClaricppExpr expr) {
        return API::c_str(API::to_cpp_ref(expr).repr());
    }

    const char *claricpp_expr_type_name(const ClaricppExpr expr) {
        return API::c_str(API::to_cpp_ref(expr).type_name());
    }

    const char *claricpp_expr_op_name(const ClaricppExpr expr) {
        return API::c_str(API::to_cpp_ref(expr).op->op_name());
    }

    CUID_T claricpp_expr_cuid(const ClaricppExpr expr) { return API::to_cpp_ref(expr).cuid; }

    CUID_T claricpp_expr_op_cuid(const ClaricppExpr expr) { return API::to_cpp_ref(expr).op->cuid; }
}
