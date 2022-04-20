/**
 * @file
 * @brief This file contains constants used within the simplifications directory
 */
#ifndef R_SRC_SIMPLIFY_CONSTANTS_HPP_
#define R_SRC_SIMPLIFY_CONSTANTS_HPP_

#include "../expr.hpp"


namespace Simplify {

    // Define a custom log class for simplifications
    UTIL_LOG_DEFINE_LOG_CLASS(SimplifyLog)

    /** The type each top level simplifier must have
     *  Note: takes in a Factory::Ptr (as opposed to a raw pointer) since it may return the input
     */
    using Func = Expr::BasePtr(const Expr::BasePtr &);

    /** A vector of simplifier functions */
    using Vec = std::vector<Func *>;

    /** A map of Op CUIDs to SimpVecs */
    using Map = std::map<CUID::CUID, Vec>;

} // namespace Simplify

#endif
