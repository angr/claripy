/**
 * @file
 * @brief Define the simplify method
 */
#ifndef __SIMPLIFICATIONS_SIMPLIFY_HPP__
#define __SIMPLIFICATIONS_SIMPLIFY_HPP__

#include "../ast/forward_declarations.hpp"


namespace Simplifications {

    /** Simplify old and return the result */
    AST::Base simplify(const AST::Base &old);

} // namespace Simplifications

#endif
