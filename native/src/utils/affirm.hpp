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

    /** If not b, throw T(msg); */
    template <typename B, typename T, typename S> void affirm(const B b, const S msg) {
        if (!b) {
            throw T(msg);
        }
    }

} // namespace Utils

#endif
