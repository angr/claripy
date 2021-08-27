/**
 * @file
 * \ingroup utils
 * @brief This file defines a method which asserts a condition, and if false throws an exception
 * We use the word affirm since C libraries like to define assert as a macro
 */
#ifndef R_UTILS_AVG_HPP_
#define R_UTILS_AVG_HPP_


namespace Utils {

    /** Average (a+b)/2 but handles overflow / underflow
     *  Note: avg rounds down
     */
    template <typename T> constexpr inline T avg(T a, T b) {
        static_assert(-2 >> 1 == -1, "Avg assumes << is arithmetic, for this system it is not.");
        return (a & b) + ((a ^ b) >> 1);
    }

} // namespace Utils

#endif
