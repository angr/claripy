/**
 * @file
 * @brief This file contains constants used within the simplifications directory
 */
#ifndef __SIMPLIFICATION_CONSTANTS_HPP__
#define __SIMPLIFICATION_CONSTANTS_HPP__

#include "../expression.hpp"


namespace Simplification {

    // Define a custom log class for simplifications
    UTILS_LOG_DEFINE_LOG_CLASS(SLog)

    /** The type each top level simplifier must have
     *  Note: takes in a Factory::Ptr (as opposed to a raw pointer) since it may return the input
     */
    using SimplifierFunc = Factory::Ptr<Expression::Base>(const Factory::Ptr<Expression::Base> &);

} // namespace Simplification

#endif
