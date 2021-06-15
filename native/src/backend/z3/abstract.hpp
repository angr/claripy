/**
 * @file
 * @brief This file defines how the Z3 backend converts Z3 ASTs into Claricpp Expressions
 */
#ifndef R_BACKEND_Z3_ABSTRACT_HPP_
#define R_BACKEND_Z3_ABSTRACT_HPP_

#include "constants.hpp"

#include "../../create.hpp"


namespace Backend::Z3::Abstract {

    /** A boolean expression
     *  Warning: Should not be inline b/c of ODR rules
     */
    template <bool B> const auto bool_ { Create::literal(B) };


} // namespace Backend::Z3::Abstract

#endif
