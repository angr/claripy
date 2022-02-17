/**
 * @file
 * \ingroup api
 */
#include "cpp.hpp"

extern "C" {

    ClaricppExpr claricpp_expr_make_like_annotations(const ClaricppExpr old, ClaricppSPAV spav) {
        API_FUNC_START
        auto ret { API::to_c(Expr::make_like(API::to_cpp(old), std::move(API::to_cpp(spav)))) };
        API::free(spav);
        return ret;
        API_FUNC_END
    }

    HASH_T claricpp_expr_hash(const ClaricppExpr expr) {
        API_FUNC_START
        return API::to_cpp_ref(expr).hash;
        API_FUNC_END
    }

    BOOL claricpp_expr_is_bits(const ClaricppExpr expr) {
        API_FUNC_START
        return API::bool_(dynamic_cast<CTSC<Expr::Bits>>(API::to_cpp(expr).get()) != nullptr);
        API_FUNC_END
    }

    SIZE_T claricpp_expr_bit_length(const ClaricppExpr expr) {
        API_FUNC_START
        return Expr::get_bit_length(API::to_cpp(expr));
        API_FUNC_END
    }

    BOOL claricpp_expr_symbolic(const ClaricppExpr expr) {
        API_FUNC_START
        return API::bool_(API::to_cpp_ref(expr).symbolic);
        API_FUNC_END
    }

    ClaricppSPAV claricpp_expr_annotations(const ClaricppExpr expr) {
        API_FUNC_START
        const auto &ret { API::to_cpp_ref(expr).annotations };
        if (LIKELY(ret == nullptr)) {
            return { nullptr };
        }
        return API::copy_to_c(ret); // Can't move a reference to a const object
        API_FUNC_END
    }

    //    @TODO: ClaricppArg claricpp_expr_arg(const ClaricppExpr expr, const UINT index) {
    //    const auto &op { API::to_cpp_ref(expr).op };
    //    UTIL_ASSERT_NOT_NULL_DEBUG(op);
    //    std::vector<Op::ArgVar> ret;
    //    op->python_children(ret);
    //        return API::to_arr(std::move(ret));
    //    }

    ARRAY_OUT(ClaricppArg) claricpp_expr_args(const ClaricppExpr expr) {
        API_FUNC_START
        const auto &ex { API::to_cpp(expr) };
        UTIL_ASSERT_NOT_NULL_DEBUG(ex);
        const auto &op { ex->op };
        UTIL_ASSERT_NOT_NULL_DEBUG(op);
        std::vector<Op::ArgVar> vec;
        op->python_children(vec);
        // For ops that need their size in args...
        if (CUID::is_any_t<const Op::Base, Op::Literal, Op::Symbol>(op)) {
            if (CUID::is_any_t<const Expr::Base, Expr::Bool, Expr::BV>(ex)) {
                UTIL_ASSERT(Util::Err::Index, vec.size() >= 1,
                            "BV / Bool leaves should have at least 1 arg");
                auto ret { API::new_arr<ClaricppArg>(1 + vec.size()) };
                ret.arr[0] = API::to_c<Op::ArgVar>(std::move(vec[0]));
                ret.arr[1].type = ClaricppTypeEnumU64;
                ret.arr[1].data.prim.u64 = Expr::get_bit_length(ex);
                for (SIZE_T i { 2 }; i < ret.len; ++i) {
                    ret.arr[i] = API::to_c(std::move(vec[i - 1]));
                }
                return ret;
            }
        }
        return API::to_arr(std::move(vec));
        API_FUNC_END
    }

    const char *claricpp_expr_repr(const ClaricppExpr expr) {
        API_FUNC_START
        return API::c_str(API::to_cpp_ref(expr).repr());
        API_FUNC_END
    }

    const char *claricpp_expr_type_name(const ClaricppExpr expr) {
        API_FUNC_START
        return API::to_cpp_ref(expr).type_name();
        API_FUNC_END
    }

    const char *claricpp_expr_op_name(const ClaricppExpr expr) {
        API_FUNC_START
        return API::to_cpp_ref(expr).op->op_name();
        API_FUNC_END
    }

    CUID_T claricpp_expr_cuid(const ClaricppExpr expr) {
        API_FUNC_START
        return API::to_cpp_ref(expr).cuid;
        API_FUNC_END
    }

    CUID_T claricpp_expr_op_cuid(const ClaricppExpr expr) {
        API_FUNC_START
        return API::to_cpp_ref(expr).op->cuid;
        API_FUNC_END
    }
}
