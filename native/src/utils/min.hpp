/**
 * @file
 * \ingroup utils
 * @brief This file defines various min functions
 */
#ifndef R_UTILS_MIN_HPP_
#define R_UTILS_MIN_HPP_


namespace Utils::Min {

    /** Return the min argument, takes in it's parameters by value
     *  Unlike std::min, this will not return a dangling reference
     *  If equal, returns the first value
     */
    template <typename T> constexpr T value(const T a, const T b) { return a <= b ? a : b; }

} // namespace Utils::Min

#endif
