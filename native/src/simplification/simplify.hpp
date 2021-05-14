/**
 * @file
 * @brief Define the simplify method
 */
#ifndef R_SIMPLIFICATION_SIMPLIFY_HPP_
#define R_SIMPLIFICATION_SIMPLIFY_HPP_

#include "op_map.hpp"

#include "../expression.hpp"


namespace Simplification {

    /** Simplify old and return the result */
    inline Factory::Ptr<Expression::Base> simplify(const Factory::Ptr<Expression::Base> &old) {
        if (const auto itr { op_map.find(old->op->cuid) }; itr != op_map.end()) {
            return itr->second(old);
        }
        else {
            Utils::Log::verbose(
                "Simplify found no suitable claricpp simplifier for the given expression");
            return old;
        }
    }

} // namespace Simplification

#endif
