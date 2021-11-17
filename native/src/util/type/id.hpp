/**
 * @file
 * \ingroup util
 * @brief This file defines a type id function
 * C++'s builtin typeid function should not be used for non-debugging.
 * It's IDs are not unique, and they can change during each compilation
 */
#ifndef R_UTIL_TYPE_ID_HPP_
#define R_UTIL_TYPE_ID_HPP_

#include "../../constants.hpp"
#include "../inc.hpp"


namespace Util::Type {

    /** An improved version of C++'s typeid function */
    template <typename T> inline UInt id() noexcept {
        const static UInt ret { inc() };
        return ret;
    }

    /** An improved version of C++'s typeid function */
    template <typename T> inline UInt id(T &&) noexcept { return id<T>(); }

} // namespace Util::Type

#endif
