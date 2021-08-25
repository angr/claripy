/**
 * @file
 * \ingroup utils
 * @brief This file defines a method which asserts a condition, and if false throws an exception
 * We use the word affirm since C libraries like to define assert as a macro
 */
#ifndef R_UTILS_AVG_HPP_
#define R_UTILS_AVG_HPP_


namespace Utils {

    /** Average (a+b)/2 but handles overflow / underflow */
    template <typename T> constexpr inline T avg(T a, T b) { return (a & b) + ((a ^ b) >> 1); }

} // namespace Utils

#endif
