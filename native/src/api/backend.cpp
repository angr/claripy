/**
 * @file
 * \ingroup api
 */
#include "cpp.hpp"

// Helpers

/** Creates a vector of extra_constraints */
static inline auto to_con_vec(ARRAY_IN(ClaricppExpr) constraints, const SIZE_T len) {
    std::vector<Expr::RawPtr> con;
    con.resize(len);
    for (UInt i { 0 }; i < len; ++i) {
        con[i] = API::to_cpp(constraints[i]).get(); // NOLINT (false positive)
    }
    return con;
}

/********************************************************************/
/*                               Base                               */
/********************************************************************/

extern "C" {

    const char *claricpp_backend_name(ClaricppBackend bk) {
        API_FUNC_START
        return API::to_cpp(bk)->name();
        API_FUNC_END
    }

    BOOL claricpp_backend_handles(const ClaricppBackend bk, const ClaricppExpr expr) {
        API_FUNC_START
        return API::bool_(API::to_cpp(bk)->handles(API::to_cpp(expr).get()));
        API_FUNC_END
    }

    ClaricppExpr claricpp_backend_simplify(const ClaricppBackend bk, const ClaricppExpr expr) {
        API_FUNC_START
        return API::to_c(API::to_cpp(bk)->simplify(API::to_cpp(expr).get()));
        API_FUNC_END
    }

    void claricpp_backend_downsize(const ClaricppBackend bk) {
        API_FUNC_START
        return API::to_cpp(bk)->downsize();
        API_FUNC_END_NO_RETURN
    }

    void claricpp_backend_clear_persistent_data(const ClaricppBackend bk) {
        API_FUNC_START
        return API::to_cpp(bk)->clear_persistent_data();
        API_FUNC_END_NO_RETURN
    }
}

/********************************************************************/
/*                                Z3                                */
/********************************************************************/

extern "C" {

    ClaricppBackend claricpp_backend_z3_new() {
        API_FUNC_START
        return { API::to_c(Util::make_derived_shared<Backend::Base, Backend::Z3::Z3>()) };
        API_FUNC_END
    }

    ClaricppSolver claricpp_backend_z3_tls_solver(const ClaricppBackend z3, const Z3U timeout) {
        API_FUNC_START
        return API::to_c(API::to_cpp_down_ref<Backend::Z3::Z3>(z3).tls_solver<false>(timeout));
        API_FUNC_END
    }

    ClaricppSolver claricpp_backend_z3_new_tls_solver(const ClaricppBackend z3, const Z3U timeout) {
        API_FUNC_START
        return API::to_c(API::to_cpp_down_ref<Backend::Z3::Z3>(z3).tls_solver<true>(timeout));
        API_FUNC_END
    }

    void claricpp_backend_z3_add_tracked(const ClaricppBackend z3, const ClaricppSolver solver,
                                         const ClaricppExpr constraint) {
        API_FUNC_START
        API::to_cpp_down_ref<Backend::Z3::Z3>(z3).add<true>(API::to_cpp_ref(solver),
                                                            API::to_cpp(constraint).get());
        API_FUNC_END_NO_RETURN
    }

    void claricpp_backend_z3_add_vec_tracked(const ClaricppBackend z3, const ClaricppSolver solver,
                                             ARRAY_IN(ClaricppExpr) constraints, const SIZE_T len) {
        API_FUNC_START
        API::to_cpp_down_ref<Backend::Z3::Z3>(z3).add<true>(API::to_cpp_ref(solver),
                                                            to_con_vec(constraints, len));
        API_FUNC_END_NO_RETURN
    }

    void claricpp_backend_z3_add_untracked(const ClaricppBackend z3, const ClaricppSolver solver,
                                           const ClaricppExpr constraint) {
        API_FUNC_START
        API::to_cpp_down_ref<Backend::Z3::Z3>(z3).add<false>(API::to_cpp_ref(solver),
                                                             API::to_cpp(constraint).get());
        API_FUNC_END_NO_RETURN
    }

    void claricpp_backend_z3_add_vec_untracked(const ClaricppBackend z3,
                                               const ClaricppSolver solver,
                                               ARRAY_IN(ClaricppExpr) constraints,
                                               const SIZE_T len) {
        API_FUNC_START
        API::to_cpp_down_ref<Backend::Z3::Z3>(z3).add<false>(API::to_cpp_ref(solver),
                                                             to_con_vec(constraints, len));
        API_FUNC_END_NO_RETURN
    }

    BOOL claricpp_backend_z3_satisfiable(const ClaricppBackend z3, const ClaricppSolver solver) {
        API_FUNC_START
        return API::bool_(
            API::to_cpp_down_ref<Backend::Z3::Z3>(z3).satisfiable(API::to_cpp_ref(solver)));
        API_FUNC_END
    }

    BOOL claricpp_backend_z3_satisfiable_ec(const ClaricppBackend z3, const ClaricppSolver solver,
                                            ARRAY_IN(ClaricppExpr) extra_constraints,
                                            const SIZE_T len) {
        API_FUNC_START
        return API::bool_(API::to_cpp_down_ref<Backend::Z3::Z3>(z3).satisfiable(
            API::to_cpp_ref(solver), to_con_vec(extra_constraints, len)));
        API_FUNC_END
    }

    BOOL claricpp_backend_z3_solution(const ClaricppBackend z3, const ClaricppExpr expr,
                                      const ClaricppExpr sol, const ClaricppSolver solver) {
        API_FUNC_START
        return API::bool_(API::to_cpp_down_ref<Backend::Z3::Z3>(z3).solution(
            API::to_cpp(expr).get(), API::to_cpp(sol).get(), API::to_cpp_ref(solver)));
        API_FUNC_END
    }

    BOOL claricpp_backend_z3_solution_ec(const ClaricppBackend z3, const ClaricppExpr expr,
                                         const ClaricppExpr sol, const ClaricppSolver solver,
                                         ARRAY_IN(ClaricppExpr) extra_constraints,
                                         const SIZE_T len) {
        API_FUNC_START
        return API::bool_(API::to_cpp_down_ref<Backend::Z3::Z3>(z3).solution(
            API::to_cpp(expr).get(), API::to_cpp(sol).get(), API::to_cpp_ref(solver),
            to_con_vec(extra_constraints, len)));
        API_FUNC_END
    }

    int64_t claricpp_backend_z3_min_signed(const ClaricppBackend z3, const ClaricppExpr expr,
                                           const ClaricppSolver solver) {
        API_FUNC_START
        return API::to_cpp_down_ref<Backend::Z3::Z3>(z3).template min<true>(
            API::to_cpp(expr).get(), API::to_cpp_ref(solver));
        API_FUNC_END
    }

    int64_t claricpp_backend_z3_min_signed_ec(const ClaricppBackend z3, const ClaricppExpr expr,
                                              const ClaricppSolver solver,
                                              ARRAY_IN(ClaricppExpr) extra_constraints,
                                              const SIZE_T len) {
        API_FUNC_START
        return API::to_cpp_down_ref<Backend::Z3::Z3>(z3).template min<true>(
            API::to_cpp(expr).get(), API::to_cpp_ref(solver), to_con_vec(extra_constraints, len));
        API_FUNC_END
    }

    uint64_t claricpp_backend_z3_min_unsigned(const ClaricppBackend z3, const ClaricppExpr expr,
                                              const ClaricppSolver solver) {
        API_FUNC_START
        return API::to_cpp_down_ref<Backend::Z3::Z3>(z3).template min<false>(
            API::to_cpp(expr).get(), API::to_cpp_ref(solver));
        API_FUNC_END
    }

    uint64_t claricpp_backend_z3_min_unsigned_ec(const ClaricppBackend z3, const ClaricppExpr expr,
                                                 const ClaricppSolver solver,
                                                 ARRAY_IN(ClaricppExpr) extra_constraints,
                                                 const SIZE_T len) {
        API_FUNC_START
        return API::to_cpp_down_ref<Backend::Z3::Z3>(z3).template min<false>(
            API::to_cpp(expr).get(), API::to_cpp_ref(solver), to_con_vec(extra_constraints, len));
        API_FUNC_END
    }

    int64_t claricpp_backend_z3_max_signed(const ClaricppBackend z3, const ClaricppExpr expr,
                                           const ClaricppSolver solver) {
        API_FUNC_START
        return API::to_cpp_down_ref<Backend::Z3::Z3>(z3).template max<true>(
            API::to_cpp(expr).get(), API::to_cpp_ref(solver));
        API_FUNC_END
    }

    int64_t claricpp_backend_z3_max_signed_ec(const ClaricppBackend z3, const ClaricppExpr expr,
                                              const ClaricppSolver solver,
                                              ARRAY_IN(ClaricppExpr) extra_constraints,
                                              const SIZE_T len) {
        API_FUNC_START
        return API::to_cpp_down_ref<Backend::Z3::Z3>(z3).template max<true>(
            API::to_cpp(expr).get(), API::to_cpp_ref(solver), to_con_vec(extra_constraints, len));
        API_FUNC_END
    }

    uint64_t claricpp_backend_z3_max_unsigned(const ClaricppBackend z3, const ClaricppExpr expr,
                                              const ClaricppSolver solver) {
        API_FUNC_START
        return API::to_cpp_down_ref<Backend::Z3::Z3>(z3).template max<false>(
            API::to_cpp(expr).get(), API::to_cpp_ref(solver));
        API_FUNC_END
    }

    uint64_t claricpp_backend_z3_max_unsigned_ec(const ClaricppBackend z3, const ClaricppExpr expr,
                                                 const ClaricppSolver solver,
                                                 ARRAY_IN(ClaricppExpr) extra_constraints,
                                                 const SIZE_T len) {
        API_FUNC_START
        return API::to_cpp_down_ref<Backend::Z3::Z3>(z3).template max<false>(
            API::to_cpp(expr).get(), API::to_cpp_ref(solver), to_con_vec(extra_constraints, len));
        API_FUNC_END
    }

    ARRAY_OUT(ClaricppExpr)
    claricpp_backend_z3_unsat_core(const ClaricppBackend z3, const ClaricppSolver solver) {
        API_FUNC_START
        return API::to_arr(
            API::to_cpp_down_ref<Backend::Z3::Z3>(z3).unsat_core(API::to_cpp_ref(solver)));
        API_FUNC_END
    }

    ARRAY_OUT(ClaricppPrim)
    claricpp_backend_z3_eval(const ClaricppBackend z3, const ClaricppExpr expr,
                             const ClaricppSolver solver, const SIZE_T n) {
        API_FUNC_START
        return API::to_arr(API::to_cpp_down_ref<Backend::Z3::Z3>(z3).eval(
            API::to_cpp(expr).get(), API::to_cpp_ref(solver), n));
        API_FUNC_END
    }

    ARRAY_OUT(ClaricppPrim)
    claricpp_backend_z3_eval_ec(const ClaricppBackend z3, const ClaricppExpr expr,
                                const ClaricppSolver solver, const SIZE_T n,
                                ARRAY_IN(ClaricppExpr) extra_constraints, const SIZE_T len) {
        API_FUNC_START
        return API::to_arr(API::to_cpp_down_ref<Backend::Z3::Z3>(z3).eval(
            API::to_cpp(expr).get(), API::to_cpp_ref(solver), n,
            to_con_vec(extra_constraints, len)));
        API_FUNC_END
    }

    DOUBLE_ARRAY_OUT(ClaricppPrim)
    claricpp_backend_z3_batch_eval(const ClaricppBackend z3, ARRAY_IN(ClaricppExpr) exprs,
                                   const SIZE_T exprs_len, const ClaricppSolver solver,
                                   const SIZE_T n) {
        API_FUNC_START
        return API::to_double_arr(API::to_cpp_down_ref<Backend::Z3::Z3>(z3).batch_eval(
            to_con_vec(exprs, exprs_len), API::to_cpp_ref(solver), n));
        API_FUNC_END
    }

    DOUBLE_ARRAY_OUT(ClaricppPrim)
    claricpp_backend_z3_batch_eval_ec(const ClaricppBackend z3, ARRAY_IN(ClaricppExpr) exprs,
                                      const SIZE_T exprs_len, const ClaricppSolver solver,
                                      const SIZE_T n, ARRAY_IN(ClaricppExpr) extra_constraints,
                                      const SIZE_T ec_len) {
        API_FUNC_START
        return API::to_double_arr(API::to_cpp_down_ref<Backend::Z3::Z3>(z3).batch_eval(
            to_con_vec(exprs, exprs_len), API::to_cpp_ref(solver), n,
            to_con_vec(extra_constraints, ec_len)));
        API_FUNC_END
    }
}

/********************************************************************/
/*                             Concrete                             */
/********************************************************************/
