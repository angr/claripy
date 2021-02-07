/**
 * @file
 * \ingroup utils
 * @brief This file defines a method for determining if T is in a typelist Args...
 */
#ifndef __UTILS_ISIN_HPP__
#define __UTILS_ISIN_HPP__

#include "is_same.hpp"


namespace Utils {

    /** Return true if T in Args */
    template <typename T, typename... Args>
    const inline constexpr bool qualified_is_in { (is_exactly_same<T, Args> || ...) };

    /** Return true if T in Args; ignores constness of everything */
    template <typename T, typename... Args>
    const inline constexpr bool is_in_ignore_const { (is_same_ignore_const<T, Args> || ...) };

    /** Return true if is_ancestor<Args[i], T> for any i */
    template <typename T, typename... Args>
    const inline constexpr bool ancestor_is_in { (is_ancestor<Args, T> || ...) };

} // namespace Utils

#endif
