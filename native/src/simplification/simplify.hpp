/**
 * @file
 * @brief Define the simplify method
 */
#ifndef __SIMPLIFICATION_SIMPLIFY_HPP__
#define __SIMPLIFICATION_SIMPLIFY_HPP__

#include "../ast/forward_declarations.hpp"


namespace Simplification {

    /** Simplify old and return the result */
    AST::Base simplify(const AST::Base &old);

} // namespace Simplifications

#endif
