/**
 * @file
 * @brief This file defines how the Z3 backend converts Z3 ASTs into Claricpp Expressions
 */
#ifndef R_BACKEND_Z3_ABSTRACT_HPP_
#define R_BACKEND_Z3_ABSTRACT_HPP_

#include "constants.hpp"

#include "../../create.hpp"


namespace Backend::Z3::Abstract {

    namespace Private {

        /** A z3 thread local raw context that is the same as the z3::context */
        Z3_context mctx = Private::tl_ctx;
    } // namespace Private

    /** A boolean expression
     *  Warning: Should not be inline b/c of ODR rules
     */
    template <bool B> const auto bool_ { Create::literal(B) };


} // namespace Backend::Z3::Abstract

#endif
