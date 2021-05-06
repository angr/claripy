/**
 * @file
 * @brief This file defines the contexts that the z3 backend uses
 */
#ifndef __BACKEND_Z3_TLCTX_HPP__
#define __BACKEND_Z3_TLCTX_HPP__

#include <z3++.h>


namespace Backend::Z3::Private {

    /** A thread local context all Z3 exprs should use */
    inline thread_local z3::context tl_ctx;

} // namespace Backend::Z3::Private

#endif
