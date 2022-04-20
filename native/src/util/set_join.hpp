/**
 * @file
 * \ingroup util
 * @brief This file defines a method to join a set of set<T>'s together
 */
#ifndef R_SRC_UTIL_SETJOIN_HPP_
#define R_SRC_UTIL_SETJOIN_HPP_

#include "private/set_insert.hpp"


namespace Util {

    /** Joins a set of std::set<T>'s into one */
    template <typename T, typename... Args>
    inline std::set<T> set_join(const std::set<T> &first, Args &&...args) {
        auto ret { std::set<T>(first) };
        (Private::set_insert<T>(ret, std::forward<Args>(args)), ...);
        return ret;
    }

} // namespace Util

#endif
