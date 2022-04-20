/**
 * @file
 * \ingroup util
 * @brief This file defines the str_prefix function
 */
#ifndef R_SRC_UTIL_STRPREFIX_HPP_
#define R_SRC_UTIL_STRPREFIX_HPP_

#include "strlen.hpp"


namespace Util {

    /** Return true if a starts with b */
    constexpr bool str_prefix(const char *a, const char *b) noexcept {
        if (Util::strlen(a) < Util::strlen(b)) {
            return false;
        }
        for (; *b; ++a, ++b) {
            if (*a != *b) {
                return false;
            }
        }
        return true;
    }
} // namespace Util

#endif
