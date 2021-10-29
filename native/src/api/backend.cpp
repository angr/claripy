/**
 * @file
 * \ingroup api
 */
#include "cpp.hpp"

/********************************************************************/
/*                               Base                               */
/********************************************************************/

const char *claricpp_backend_name(ClaricppBackend bk) {
    return API::to_cpp(bk)->name();
}

bool claricpp_backend_handles(const ClaricppBackend bk, const ClaricppExpr expr) {
    return API::to_cpp(bk)->handles(API::to_cpp(expr).get());
}

ClaricppExpr claricpp_backend_simplify(const ClaricppBackend bk, const ClaricppExpr expr) {
    return API::to_c(API::to_cpp(bk)->simplify(API::to_cpp(expr).get()));
}

void claricpp_backend_downsize(const ClaricppBackend bk) {
    return API::to_cpp(bk)->downsize();
}

void claricpp_backend_clear_persistent_data(const ClaricppBackend bk) {
    return API::to_cpp(bk)->clear_persistent_data();
}

ClaricppBIM claricpp_backend_get_big_int_mode() {
    return API::mode(Backend::Base::big_int_mode());
}

ClaricppBIM claricpp_backend_set_big_int_mode(const ClaricppBIM m) {
    return API::mode(Backend::Base::big_int_mode(API::mode(m)));
}

/********************************************************************/
/*                                Z3                                */
/********************************************************************/

ClaricppBackend claricpp_backend_z3_new() {
    return { API::to_c(Util::make_derived_shared<Backend::Base, Backend::Z3::Z3>()) };
}

ClaricppSolver claricpp_backend_z3_tls_solver(const ClaricppBackend z3, const Z3U timeout) {
    auto z3_cpp { dynamic_cast<Backend::Z3::Z3 *>(API::to_cpp(z3).get()) };
    UTILS_AFFIRM_NOT_NULL_DEBUG(z3_cpp);
    return API::to_c(z3_cpp->tls_solver<false>(timeout));
}

ClaricppSolver claricpp_backend_z3_new_tls_solver(const ClaricppBackend z3, const Z3U timeout) {
    auto z3_cpp { dynamic_cast<Backend::Z3::Z3 *>(API::to_cpp(z3).get()) };
    UTILS_AFFIRM_NOT_NULL_DEBUG(z3_cpp);
    return API::to_c(z3_cpp->tls_solver<true>(timeout));
}

/********************************************************************/
/*                             Concrete                             */
/********************************************************************/
