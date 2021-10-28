/**
 * @file
 * \ingroup api
 */
#include "cpp.hpp"

/********************************************************************/
/*                               Base                               */
/********************************************************************/

PyStr claricpp_backend_name(ClaricppBackend bk) {
    return API::to_cpp(bk)->name();
}

ClaricppExpr claricpp_backend_simplify(const ClaricppBackend bk, const ClaricppExpr expr) {
    return API::to_c(API::to_cpp(bk)->simplify(API::to_cpp(expr).get()));
}

bool claricpp_backend_handles(const ClaricppBackend bk, const ClaricppExpr expr) {
    return API::to_cpp(bk)->handles(API::to_cpp(expr).get());
}

void claricpp_backend_downsize(const ClaricppBackend bk) {
    return API::to_cpp(bk)->downsize();
}

void claricpp_backend_clear_persistent_data(const ClaricppBackend bk) {
    return API::to_cpp(bk)->clear_persistent_data();
}

/********************************************************************/
/*                                Z3                                */
/********************************************************************/

/********************************************************************/
/*                             Concrete                             */
/********************************************************************/