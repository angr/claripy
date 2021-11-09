/**
 * @file
 * @brief This file contains constants used within the simplifications directory
 */
#ifndef R_SIMPLIFICATION_CONSTANTS_HPP_
#define R_SIMPLIFICATION_CONSTANTS_HPP_

#include "../expr.hpp"


namespace Simplification {

    // Define a custom log class for simplifications
    UTIL_LOG_DEFINE_LOG_CLASS(SLog)

    /** The type each top level simplifier must have
     *  Note: takes in a Factory::Ptr (as opposed to a raw pointer) since it may return the input
     */
    using SimplifierFunc = Expr::BasePtr(const Expr::BasePtr &);

} // namespace Simplification

#endif
