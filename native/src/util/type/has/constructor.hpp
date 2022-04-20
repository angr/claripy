/**
 * @file
 * \ingroup util
 * @brief This file defines a way to check if a type T can accepts Args... args.
 * Note: unlike std::is_constructible, this can be friended to allow private constructor access
 */
#ifndef R_SRC_UTIL_TYPE_HAS_CONSTRUCTOR_HPP_
#define R_SRC_UTIL_TYPE_HAS_CONSTRUCTOR_HPP_

#include "../sfinae_test.hpp"


namespace Util::Type::Has {

    /** A struct which determines if the constructor T(Args...) is visible and exists
     *  Basically std::is_constructible but can be friended to allow private constructor access
     */
    UTIL_TYPE_SFINAETEST(constructor,                 // Name
                         T(std::declval<Args>()...),  // Condition we are checking
                         typename T, typename... Args // Template arguments
    )

} // namespace Util::Type::Has

#endif
