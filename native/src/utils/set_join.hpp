/**
 * @file
 * @brief This file defines a method to join a set of set<T>'s together
 */
#ifndef __UTILS_SET_JOIN_HPP__
#define __UTILS_SET_JOIN_HPP__

#include "private/set_join.hpp"

#include <set>


/** A namespace used for the utils directory */
namespace Utils {

    /** Joins a set of set<T>'s into one
     *  Requires at least two arguments.
     *  Can automatically deduce template types from arguments
     */
    template <typename T, typename... Args>
    std::set<T> set_join(const std::set<T> &s1, const Args... args) {
        auto ret = std::set<T>();
        Private::set_join<T>(ret, std::forward<decltype(s1)>(s1),
                             std::forward<const Args>(args)...);
        return ret;
    }

} // namespace Utils

#endif
