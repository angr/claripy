/**
 * @file
 * \ingroup util
 * @brief This file defines various max functions
 */
#ifndef R_SRC_UTIL_MAX_HPP_
#define R_SRC_UTIL_MAX_HPP_


namespace Util::Max {

    /** Return the max argument, takes in it's parameters by value
     *  Unlike std::max, this will not return a dangling reference
     *  If equal, returns the first value
     */
    template <typename T> constexpr T value(const T a, const T b) {
        return a >= b ? a : b;
    }

} // namespace Util::Max

#endif
