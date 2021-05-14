/**
 * @file
 * @brief This file defines the contexts that the z3 backend uses
 */
#ifndef R_BACKEND_Z3_TLCTX_HPP_
#define R_BACKEND_Z3_TLCTX_HPP_

#include <z3++.h>


namespace Backend::Z3::Private {

    /** A thread local context all Z3 exprs should use */
    inline thread_local z3::context tl_ctx;

} // namespace Backend::Z3::Private

#endif
