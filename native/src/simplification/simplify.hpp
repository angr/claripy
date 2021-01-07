/**
 * @file
 * @brief Define the simplify method
 */
#ifndef __SIMPLIFICATION_SIMPLIFY_HPP__
#define __SIMPLIFICATION_SIMPLIFY_HPP__

#include "../expression/forward_declarations.hpp"


namespace Simplification {

    /** Simplify old and return the result */
    Expression::Base simplify(const Expression::Base &old);

} // namespace Simplification

#endif
