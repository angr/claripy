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

    const char *claricpp_backend_name(ClaricppBackend bk) { return API::to_cpp(bk)->name(); }

    BOOL claricpp_backend_handles(const ClaricppBackend bk, const ClaricppExpr expr) {
        return API::bool_(API::to_cpp(bk)->handles(API::to_cpp(expr).get()));
    }

    ClaricppExpr claricpp_backend_simplify(const ClaricppBackend bk, const ClaricppExpr expr) {
        return API::to_c(API::to_cpp(bk)->simplify(API::to_cpp(expr).get()));
    }

    void claricpp_backend_downsize(const ClaricppBackend bk) { return API::to_cpp(bk)->downsize(); }

    void claricpp_backend_clear_persistent_data(const ClaricppBackend bk) {
        return API::to_cpp(bk)->clear_persistent_data();
    }

    ClaricppBIM claricpp_backend_get_big_int_mode() {
        return API::mode(Backend::Base::big_int_mode());
    }

    ClaricppBIM claricpp_backend_set_big_int_mode(const ClaricppBIM m) {
        return API::mode(Backend::Base::big_int_mode(API::mode(m)));
    }
}

/********************************************************************/
/*                                Z3                                */
/********************************************************************/

extern "C" {

    ClaricppBackend claricpp_backend_z3_new() {
        return { API::to_c(Util::make_derived_shared<Backend::Base, Backend::Z3::Z3>()) };
    }

    ClaricppSolver claricpp_backend_z3_tls_solver(const ClaricppBackend z3, const Z3U timeout) {
        return API::to_c(API::to_cpp_down_ref<Backend::Z3::Z3>(z3).tls_solver<false>(timeout));
    }

    ClaricppSolver claricpp_backend_z3_new_tls_solver(const ClaricppBackend z3, const Z3U timeout) {
        return API::to_c(API::to_cpp_down_ref<Backend::Z3::Z3>(z3).tls_solver<true>(timeout));
    }

    void claricpp_backend_z3_add_tracked(const ClaricppBackend z3, const ClaricppSolver solver,
                                         const ClaricppExpr constraint) {
        API::to_cpp_down_ref<Backend::Z3::Z3>(z3).add<true>(API::to_cpp_ref(solver),
                                                            API::to_cpp(constraint).get());
    }

    void claricpp_backend_z3_add_vec_tracked(const ClaricppBackend z3, const ClaricppSolver solver,
                                             ARRAY_IN(ClaricppExpr) constraints, const SIZE_T len) {
        API::to_cpp_down_ref<Backend::Z3::Z3>(z3).add<true>(API::to_cpp_ref(solver),
                                                            to_con_vec(constraints, len));
    }

    void claricpp_backend_z3_add_untracked(const ClaricppBackend z3, const ClaricppSolver solver,
                                           const ClaricppExpr constraint) {
        API::to_cpp_down_ref<Backend::Z3::Z3>(z3).add<false>(API::to_cpp_ref(solver),
                                                             API::to_cpp(constraint).get());
    }

    void claricpp_backend_z3_add_vec_untracked(const ClaricppBackend z3,
                                               const ClaricppSolver solver,
                                               ARRAY_IN(ClaricppExpr) constraints,
                                               const SIZE_T len) {
        API::to_cpp_down_ref<Backend::Z3::Z3>(z3).add<false>(API::to_cpp_ref(solver),
                                                             to_con_vec(constraints, len));
    }

    BOOL claricpp_backend_z3_satisfiable(const ClaricppBackend z3, const ClaricppSolver solver) {
        return API::bool_(
            API::to_cpp_down_ref<Backend::Z3::Z3>(z3).satisfiable(API::to_cpp_ref(solver)));
    }

    BOOL claricpp_backend_z3_satisfiable_ec(const ClaricppBackend z3, const ClaricppSolver solver,
                                            ARRAY_IN(ClaricppExpr) extra_constraints,
                                            const SIZE_T len) {
        return API::bool_(API::to_cpp_down_ref<Backend::Z3::Z3>(z3).satisfiable(
            API::to_cpp_ref(solver), to_con_vec(extra_constraints, len)));
    }

    BOOL claricpp_backend_z3_solution(const ClaricppBackend z3, const ClaricppExpr expr,
                                      const ClaricppExpr sol, const ClaricppSolver solver) {
        return API::bool_(API::to_cpp_down_ref<Backend::Z3::Z3>(z3).solution(
            API::to_cpp(expr).get(), API::to_cpp(sol).get(), API::to_cpp_ref(solver)));
    }

    BOOL claricpp_backend_z3_solution_ec(const ClaricppBackend z3, const ClaricppExpr expr,
                                         const ClaricppExpr sol, const ClaricppSolver solver,
                                         ARRAY_IN(ClaricppExpr) extra_constraints,
                                         const SIZE_T len) {
        return API::bool_(API::to_cpp_down_ref<Backend::Z3::Z3>(z3).solution(
            API::to_cpp(expr).get(), API::to_cpp(sol).get(), API::to_cpp_ref(solver),
            to_con_vec(extra_constraints, len)));
    }

    int64_t claricpp_backend_z3_min_signed(const ClaricppBackend z3, const ClaricppExpr expr,
                                           const ClaricppSolver solver) {
        return API::to_cpp_down_ref<Backend::Z3::Z3>(z3).template min<true>(
            API::to_cpp(expr).get(), API::to_cpp_ref(solver));
    }

    int64_t claricpp_backend_z3_min_signed_ec(const ClaricppBackend z3, const ClaricppExpr expr,
                                              const ClaricppSolver solver,
                                              ARRAY_IN(ClaricppExpr) extra_constraints,
                                              const SIZE_T len) {
        return API::to_cpp_down_ref<Backend::Z3::Z3>(z3).template min<true>(
            API::to_cpp(expr).get(), API::to_cpp_ref(solver), to_con_vec(extra_constraints, len));
    }

    uint64_t claricpp_backend_z3_min_unsigned(const ClaricppBackend z3, const ClaricppExpr expr,
                                              const ClaricppSolver solver) {
        return API::to_cpp_down_ref<Backend::Z3::Z3>(z3).template min<false>(
            API::to_cpp(expr).get(), API::to_cpp_ref(solver));
    }

    uint64_t claricpp_backend_z3_min_unsigned_ec(const ClaricppBackend z3, const ClaricppExpr expr,
                                                 const ClaricppSolver solver,
                                                 ARRAY_IN(ClaricppExpr) extra_constraints,
                                                 const SIZE_T len) {
        return API::to_cpp_down_ref<Backend::Z3::Z3>(z3).template min<false>(
            API::to_cpp(expr).get(), API::to_cpp_ref(solver), to_con_vec(extra_constraints, len));
    }

    int64_t claricpp_backend_z3_max_signed(const ClaricppBackend z3, const ClaricppExpr expr,
                                           const ClaricppSolver solver) {
        return API::to_cpp_down_ref<Backend::Z3::Z3>(z3).template max<true>(
            API::to_cpp(expr).get(), API::to_cpp_ref(solver));
    }

    int64_t claricpp_backend_z3_max_signed_ec(const ClaricppBackend z3, const ClaricppExpr expr,
                                              const ClaricppSolver solver,
                                              ARRAY_IN(ClaricppExpr) extra_constraints,
                                              const SIZE_T len) {
        return API::to_cpp_down_ref<Backend::Z3::Z3>(z3).template max<true>(
            API::to_cpp(expr).get(), API::to_cpp_ref(solver), to_con_vec(extra_constraints, len));
    }

    uint64_t claricpp_backend_z3_max_unsigned(const ClaricppBackend z3, const ClaricppExpr expr,
                                              const ClaricppSolver solver) {
        return API::to_cpp_down_ref<Backend::Z3::Z3>(z3).template max<false>(
            API::to_cpp(expr).get(), API::to_cpp_ref(solver));
    }

    uint64_t claricpp_backend_z3_max_unsigned_ec(const ClaricppBackend z3, const ClaricppExpr expr,
                                                 const ClaricppSolver solver,
                                                 ARRAY_IN(ClaricppExpr) extra_constraints,
                                                 const SIZE_T len) {
        return API::to_cpp_down_ref<Backend::Z3::Z3>(z3).template max<false>(
            API::to_cpp(expr).get(), API::to_cpp_ref(solver), to_con_vec(extra_constraints, len));
    }

    ARRAY_OUT(ClaricppExpr)
    claricpp_backend_z3_unsat_core(const ClaricppBackend z3, const ClaricppSolver solver) {
        return API::to_arr(
            API::to_cpp_down_ref<Backend::Z3::Z3>(z3).unsat_core(API::to_cpp_ref(solver)));
    }

    ARRAY_OUT(ClaricppPrim)
    claricpp_backend_z3_eval(const ClaricppBackend z3, const ClaricppExpr expr,
                             const ClaricppSolver solver, const SIZE_T n) {
        return API::to_arr(API::to_cpp_down_ref<Backend::Z3::Z3>(z3).eval(
            API::to_cpp(expr).get(), API::to_cpp_ref(solver), n));
    }

    ARRAY_OUT(ClaricppPrim)
    claricpp_backend_z3_eval_ec(const ClaricppBackend z3, const ClaricppExpr expr,
                                const ClaricppSolver solver, const SIZE_T n,
                                ARRAY_IN(ClaricppExpr) extra_constraints, const SIZE_T len) {
        return API::to_arr(API::to_cpp_down_ref<Backend::Z3::Z3>(z3).eval(
            API::to_cpp(expr).get(), API::to_cpp_ref(solver), n,
            to_con_vec(extra_constraints, len)));
    }

    DOUBLE_ARRAY_OUT(ClaricppPrim)
    claricpp_backend_z3_batch_eval(const ClaricppBackend z3, ARRAY_IN(ClaricppExpr) exprs,
                                   const SIZE_T exprs_len, const ClaricppSolver solver,
                                   const SIZE_T n) {
        return API::to_double_arr(API::to_cpp_down_ref<Backend::Z3::Z3>(z3).batch_eval(
            to_con_vec(exprs, exprs_len), API::to_cpp_ref(solver), n));
    }

    DOUBLE_ARRAY_OUT(ClaricppPrim)
    claricpp_backend_z3_batch_eval_ec(const ClaricppBackend z3, ARRAY_IN(ClaricppExpr) exprs,
                                      const SIZE_T exprs_len, const ClaricppSolver solver,
                                      const SIZE_T n, ARRAY_IN(ClaricppExpr) extra_constraints,
                                      const SIZE_T ec_len) {
        return API::to_double_arr(API::to_cpp_down_ref<Backend::Z3::Z3>(z3).batch_eval(
            to_con_vec(exprs, exprs_len), API::to_cpp_ref(solver), n,
            to_con_vec(extra_constraints, ec_len)));
    }
}

/********************************************************************/
/*                             Concrete                             */
/********************************************************************/
