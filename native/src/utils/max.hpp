/**
 * @file
 * @brief This file defines various max functions
 */
#ifndef __UTILS_MAX_HPP__
#define __UTILS_MAX_HPP__

#include <set>
#include <type_traits>


namespace Utils::Max {

    /** Return the max argument, takes in it's parameters by value
     *  Unlike std::max, this will not return a dangling reference
     *  If equal, returns the first value
     */
    template <typename T> T value(const T a, const T b) { return a >= b ? a : b; }

} // namespace Utils::Max

#endif
