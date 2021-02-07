/**
 * @file
 * @brief Define the simplify method
 */
#ifndef __SIMPLIFICATION_SIMPLIFY_HPP__
#define __SIMPLIFICATION_SIMPLIFY_HPP__

#include "../expression.hpp"


namespace Simplification {

    /** Simplify old and return the result */
    Factory::Ptr<Expression::Base> simplify(const Factory::Ptr<Expression::Base> &old);

} // namespace Simplification

#endif
