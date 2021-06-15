/**
 * @file
 * @brief This file defines the contexts that the z3 backend uses
 */
#ifndef R_BACKEND_Z3_TLCTX_HPP_
#define R_BACKEND_Z3_TLCTX_HPP_

#include <z3++.h>


namespace Backend::Z3::Private {

    /** A thread local context all Z3 exprs should use
     *  This might be inline-able, but the tests cases might violate the ODR rules
     */
    thread_local z3::context tl_ctx;

    /** A z3 thread local raw context that is the same as the z3::context
     *  This might be inline-able, but the tests cases might violate the ODR rules
     */
    thread_local Z3_context tl_raw_ctx { tl_ctx };

} // namespace Backend::Z3::Private

#endif
