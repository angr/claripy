/**
 * @file
 * @brief This file defines a method which asserts a condition, and if false throws an exception
 * We use the word affirm since C libraries like to define assert as a macro
 */
#ifndef __UTILS_AFFIRM_HPP__
#define __UTILS_AFFIRM_HPP__

#include <set>
#include <type_traits>


/** A namespace used for the utils directory */
namespace Utils {

    /** If not b, throw T(args...); */
    template <typename T, typename B, typename... Args>
    constexpr void affirm(const B b, const Args... args) {
        if (!b) {
            throw T(args...);
        }
    }

} // namespace Utils

#endif
