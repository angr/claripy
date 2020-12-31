/**
 * @file
 * \ingroup utils
 * @brief This file defines a method to join a set of set<T>'s together
 */
#ifndef __UTILS_SET_JOIN_HPP__
#define __UTILS_SET_JOIN_HPP__

#include "apply.hpp"
#include "private/set_insert.hpp"


namespace Utils {

    /** Joins a set of std::set<T>'s into one
     *  An instantiation that takes in exactly one argument
     */
    template <typename T> std::set<T> set_join(const std::set<T> &right) {
        auto ret = std::set<T>();
        Private::set_insert(ret, right);
        return ret;
    }

    /** Joins a set of std::set<T>'s into one */
    template <typename T, typename... Args>
    std::set<T> set_join(const std::set<T> &first, const Args &...args) {
        auto ret = std::set<T>();
        apply(Private::set_insert<T>, ret, first, args...);
        return ret;
    }

} // namespace Utils

#endif
