/**
 * @file
 * \ingroup util
 * @brief This file defines a way to check if a type T can accepts Args... args.
 * Note: unlike std::is_constructible, this can be friended to allow private constructor access
 */
#ifndef R_UTIL_HASCONSTRUCTOR_HPP_
#define R_UTIL_HASCONSTRUCTOR_HPP_

#include "sfinae_test.hpp"


namespace Util {

    /** A struct which determines if the constructor T(Args...) is visible and exists
     *  Basically std::is_constructible but can be friended to allow private constructor access
     */
    UTIL_SFINAETEST(has_constructor,             // Invoke this
                    HasConstructor,              // Internal class name
                    U(std::declval<Args>()...),  // Condition we are checking
                    typename T, typename... Args // Template arguments
    )

} // namespace Util

#endif
