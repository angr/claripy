/**
 * @file
 * \ingroup utils
 * @brief This file defines a method which asserts a condition, and if false throws an exception
 * We use the word affirm since C libraries like to define assert as a macro
 */
#ifndef R_UTILS_AFFIRM_HPP_
#define R_UTILS_AFFIRM_HPP_

#include "../macros.hpp"


namespace Utils {

    /** If not b, throw T(args...); */
    template <typename T, typename B, typename... Args>
    constexpr void affirm(const B b, const Args &...args) {
        if (UNLIKELY(!b)) {
            throw T(args...);
        }
    }

} // namespace Utils

#endif
