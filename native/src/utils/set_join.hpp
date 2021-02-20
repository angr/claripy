/**
 * @file
 * \ingroup utils
 * @brief This file defines a method to join a set of set<T>'s together
 */
#ifndef __UTILS_SETJOIN_HPP__
#define __UTILS_SETJOIN_HPP__

#include "private/set_insert.hpp"


namespace Utils {

    /** Joins a set of std::set<T>'s into one */
    template <typename T, typename... Args>
    inline std::set<T> set_join(const std::set<T> &first, const Args &...args) {
        auto ret { std::set<T>(first) };
        (Private::set_insert<T>(ret, args), ...);
        return ret;
    }

} // namespace Utils

#endif
