/**
 * @file
 * \ingroup utils
 * @brief This file defines a method for determining if T is in a typelist Args...
 */
#ifndef __UTILS_ISIN_HPP__
#define __UTILS_ISIN_HPP__

#include "is_ancestor.hpp"


namespace Utils {

    /** Return true if T in Args */
    template <typename T, typename... Args>
    const constexpr bool qualified_is_in = (std::is_same_v<T, Args> || ...);

    /** Return true if T in Args; transfers constness of Args[i] onto T before each comparrison */
    template <typename T, typename... Args>
    const constexpr bool ignore_const_is_in = (std::is_same_v<TransferConst<T, Args>, Args> ||
                                               ...);

    /** Return true if is_ancestor<Args[i], T> for any i */
    template <typename T, typename... Args>
    const constexpr bool ancestor_is_in = (is_ancestor<Args, T> || ...);

} // namespace Utils

#endif
