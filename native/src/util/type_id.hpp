/**
 * @file
 * \ingroup util
 * @brief This file defines a type_id function
 * C++'s builtin typeid function should not be used for non-debugging.
 * It's IDs are not unique, and they can change during each compilation
 */
#ifndef R_UTIL_TYPEID_HPP_
#define R_UTIL_TYPEID_HPP_

#include "inc.hpp"

#include "../constants.hpp"


namespace Util {

    /** An improved version of C++'s typeid function */
    template <typename T> inline UInt type_id() noexcept {
        const static UInt id { inc() };
        return id;
    }

    /** An improved version of C++'s typeid function */
    template <typename T> inline UInt type_id(T &&) noexcept { return type_id<T>(); }

} // namespace Util

#endif
