/**
 * @file
 * \ingroup utils
 * @brief This file defines a type_id function
 * C++'s builtin typeid function should not be used for non-debugging.
 * It's IDs are not unique, and they can change during each compilation
 */
#ifndef __UTILS_TYPEID_HPP__
#define __UTILS_TYPEID_HPP__

#include "inc.hpp"

#include "../constants.hpp"


namespace Utils {

    /** An improved version of C++'s typeid function */
    template <typename T> inline Constants::UInt type_id() {
        const static auto id = inc();
        return id;
    }

    /** An improved version of C++'s typeid function */
    template <typename T> inline Constants::UInt type_id(T &&) { return type_id<T>(); }

} // namespace Utils

#endif
