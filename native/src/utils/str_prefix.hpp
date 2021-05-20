/**
 * @file
 * \ingroup utils
 * @brief This file defines the str_prefix function
 */
#ifndef R_UTILS_STRPREFIX_HPP_
#define R_UTILS_STRPREFIX_HPP_

#include "strlen.hpp"


namespace Utils {

    /** Return true if a starts with b */
    constexpr bool str_prefix(const char *a, const char *b) noexcept {
        if (Utils::strlen(a) < Utils::strlen(b)) {
            return false;
        }
        for (; *b; ++a, ++b) {
            if (*a != *b) {
                return false;
            }
        }
        return true;
    }
} // namespace Utils

#endif
